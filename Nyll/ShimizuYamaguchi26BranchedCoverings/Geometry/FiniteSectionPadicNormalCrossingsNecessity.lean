/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.RegularCartier
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SingleSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Necessary incidence bound for ordinary normal crossings

This uses the ordinary normal-crossing hypothesis itself. Its supplied etale
neighbourhood provides a strict parameter product, while the original actual
two-parameter projective stalk supplies the dimension after etale extension.
The ideal pullback formula and locality of the stalk map keep every incident
original section noninvertible. The existing local factor-count theorem
then excludes a third branch.

The general `Scheme.IdealSheafData.stalkIdeal_comap` formula is proved on
affine source and target charts and applies to the actual etale morphism.
No ordinary-to-strict comparison is supplied as an assumption.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordinary normal crossings at a selected original section's actual
closed p-adic point exclude three incident labelled rational sections. -/
theorem rationalSectionPadicDivisor_card_le_two_of_isNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A)
    (hNC : (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsNormalCrossingsAt
        (rationalSectionPadicPoint p b)) :
    (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2 := by
  classical
  let X : Scheme := ProjectiveLine ℤ_[p]
  let D : X.IdealSheafData := rationalSectionPadicDivisor p A
  obtain ⟨Y, f, y, hetale, hpoint, hstrict⟩ := hNC
  have : Etale f := hetale
  have hx : rationalSectionPadicPoint p b ∈ D.support := by
    apply (rationalSectionPadicDivisor_mem_support_iff p A b).mpr
    exact ⟨b, hb, (rationalPointDelta_self b).symm ▸ dvd_zero (p : ℤ)⟩
  have hy : y ∈ (D.comap f).support :=
    (mem_support_iff_of_comap_eq D (D.comap f) f y
      (rationalSectionPadicPoint p b) hpoint rfl).mp hx
  obtain ⟨hregular, d, r, t, hrpos, hr, ht, hboundary⟩ := hstrict y hy
  let R : Type := X.presheaf.stalk (f y)
  let S : Type := Y.presheaf.stalk y
  let φ : R →+* S := (f.stalkMap y).hom
  have : IsRegularLocalRing S := hregular
  have : IsDomain S := IsRegularLocalRing.isDomain S
  have hparameters : ∃ s : Fin 2 → R, Scheme.IsRegularSystemOfParameters s := by
    have hsource : ∃ s : Fin 2 → X.presheaf.stalk (rationalSectionPadicPoint p b),
        Scheme.IsRegularSystemOfParameters s := by
      obtain ⟨_hregular, s, hs, _hequation⟩ := rationalSectionPadicPoint_parameters p b
      exact ⟨s, hs⟩
    exact (congrArg (fun x : X => ∃ s : Fin 2 → X.presheaf.stalk x,
      Scheme.IsRegularSystemOfParameters s) hpoint).mpr hsource
  obtain ⟨s, hs⟩ := hparameters
  have hsmap : Scheme.IsRegularSystemOfParameters (fun i => φ (s i)) :=
    RingHom.isRegularSystemOfParameters_map_of_flat_of_formallyUnramified_of_essFiniteType
      φ (Flat.stalkMap f y) (FormallyUnramified.stalkMap f y)
      (LocallyOfFiniteType.stalkMap f y) s hs
  let I : Projectivization ℚ (ℚ × ℚ) → X.IdealSheafData :=
    fun a => (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  have hprincipal (a : Projectivization ℚ (ℚ × ℚ)) :
      ∃ g : R, (I a).stalkIdeal (f y) = Ideal.span {g} := by
    let Da : Scheme.EffectiveCartierDivisor X := rationalSectionPadicDivisor p {a}
    have hDa : (Da : X.IdealSheafData) = I a := by
      rw [rationalSectionPadicDivisor_ideal, Finset.prod_singleton]
    obtain ⟨g, _hg, hgen⟩ := Da.property.exists_regular_stalkIdeal_generator (f y)
    exact ⟨g, (congrArg (fun J : X.IdealSheafData => J.stalkIdeal (f y)) hDa).symm.trans hgen⟩
  choose g hg using hprincipal
  have hDprod : D.stalkIdeal (f y) = Ideal.span {∏ a ∈ A, g a} := by
    dsimp only [D]
    rw [rationalSectionPadicDivisor_ideal, comap_finset_prod,
      Scheme.IdealSheafData.stalkIdeal_finset_prod]
    calc
      (∏ a ∈ A, (I a).stalkIdeal (f y)) = ∏ a ∈ A, Ideal.span {g a} :=
        Finset.prod_congr rfl (fun a _ => hg a)
      _ = Ideal.span {∏ a ∈ A, g a} := Ideal.prod_span_singleton A g
  have hprod : Ideal.span {∏ a ∈ A, φ (g a)} =
      Ideal.span {Scheme.initialParameterProduct t r hr} := by
    have hmap : (D.stalkIdeal (f y)).map φ = Ideal.span {∏ a ∈ A, φ (g a)} := by
      rw [hDprod, Ideal.map_span, Set.image_singleton, map_prod]
    exact hmap.symm.trans ((Scheme.IdealSheafData.stalkIdeal_comap D f y).symm.trans hboundary)
  apply (Finset.card_le_card (show A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b) ⊆
    A.filter (fun a => ¬IsUnit (φ (g a))) from ?_)).trans
    (nonunit_filter_card_le_two_of_parameter_product A (fun a => φ (g a))
      (fun i => φ (s i)) hsmap d r t hrpos hr ht hprod)
  intro a ha
  obtain ⟨haA, haDiv⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨haA, ?_⟩
  intro hunit
  have hsourceUnit : IsUnit (g a) := isUnit_of_map_unit φ (g a) hunit
  have htopAtImage : (I a).stalkIdeal (f y) = ⊤ :=
    (hg a).trans (Ideal.span_singleton_eq_top.mpr hsourceUnit)
  have htop : (I a).stalkIdeal (rationalSectionPadicPoint p b) = ⊤ :=
    (congrArg (fun x : X => (I a).stalkIdeal x = ⊤) hpoint).mp htopAtImage
  exact ((rationalSection_padic_stalkIdeal_eq_top_iff p a b).mp htop) haDiv

end ShimizuYamaguchi26BranchedCoverings

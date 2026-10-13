/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.RegularCartier
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SingleSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# The finite-family criterion at actual closed p-adic section points

At the closed p-adic point of a selected original rational section, the
actual finite section divisor is strictly normal crossing precisely when
at most two labelled sections pass through the point and every distinct
incident section has determinant valuation one with the selected section.

The two-parameter local ring and the single-section equation are supplied
by the actual section construction. Local principality comes from the
already constructed Cartier pullback, and the shared ring-level factor
count proves the converse. The two-branch stalk equality is transported
from the existing integral calculation rather than reproved.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem stalkIdeal_comap_eq_of_map_eq
    {X Y : Scheme} (I J : Y.IdealSheafData) (f : X ⟶ Y) [IsAffineHom f]
    (y : X) (x : Y) (hpoint : f y = x)
    (h : I.stalkIdeal x = J.stalkIdeal x) :
    (I.comap f).stalkIdeal y = (J.comap f).stalkIdeal y := by
  subst x
  rw [Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom,
    Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom]
  exact congrArg (Ideal.map (f.stalkMap y).hom) h

/-- With no other incident section, the p-adic family has the selected
section's actual stalk ideal. -/
theorem rationalSectionPadicDivisor_stalkIdeal_eq_single_of_other_disjoint
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A)
    (hother : ∀ a ∈ A, a ≠ b → ¬(p : ℤ) ∣ rationalPointDelta a b) :
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData).stalkIdeal
        (rationalSectionPadicPoint p b) =
      ((rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
        (rationalSectionPadicPoint p b) := by
  rw [rationalSectionPadicDivisor_ideal, comap_finset_prod,
    Scheme.IdealSheafData.stalkIdeal_finset_prod]
  apply Finset.prod_eq_single_of_mem b hb
  intro a ha hab
  exact ((rationalSection_padic_stalkIdeal_eq_top_iff p a b).mpr
    (hother a ha hab)).trans Ideal.one_eq_top.symm

/-- The existing integral two-branch equality transports along the actual
coefficient morphism to the p-adic family stalk. -/
theorem rationalSectionPadicDivisor_stalkIdeal_eq_pair_of_other_disjoint
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a b : Projectivization ℚ (ℚ × ℚ)) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hother : ∀ c ∈ A, c ≠ a → c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b) :
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData).stalkIdeal
        (rationalSectionPadicPoint p b) =
      (((rationalSection a).ker * (rationalSection b).ker).comap
        (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal (rationalSectionPadicPoint p b) := by
  have : IsAffineHom (ProjSpace.map ℤ ℤ_[p] 1) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (ProjSpace.isPullback_map ℤ ℤ_[p] 1).flip
      (inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℤ_[p])))))
  rw [rationalSectionPadicDivisor_ideal]
  exact stalkIdeal_comap_eq_of_map_eq (∏ c ∈ A, (rationalSection c).ker)
    ((rationalSection a).ker * (rationalSection b).ker) (ProjSpace.map ℤ ℤ_[p] 1)
    (rationalSectionPadicPoint p b) (rationalSection b (integerPrimePoint p))
    (rationalSectionPadicPoint_baseChange p b)
    (rationalSectionFamily_stalkIdeal_eq_pair_of_other_disjoint p A a b ha hb hab hother)

/-- Strict normal crossings of the actual finite p-adic divisor force at
most two of the original labelled rational sections to pass through the point. -/
theorem rationalSectionPadicDivisor_card_le_two_of_isStrictNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ))
    (hNC : (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt
        (rationalSectionPadicPoint p b)) :
    (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2 := by
  classical
  let x : ProjectiveLine ℤ_[p] := rationalSectionPadicPoint p b
  let R : Type := (ProjectiveLine ℤ_[p]).presheaf.stalk x
  let I : Projectivization ℚ (ℚ × ℚ) → (ProjectiveLine ℤ_[p]).IdealSheafData :=
    fun a => (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  have : IsRegularLocalRing R := hNC.1
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hprincipal (a : Projectivization ℚ (ℚ × ℚ)) :
      ∃ f : R, (I a).stalkIdeal x = Ideal.span {f} := by
    let D : Scheme.EffectiveCartierDivisor (ProjectiveLine ℤ_[p]) :=
      rationalSectionPadicDivisor p {a}
    have hD : (D : (ProjectiveLine ℤ_[p]).IdealSheafData) = I a := by
      rw [rationalSectionPadicDivisor_ideal, Finset.prod_singleton]
    have hcartier : (I a).IsEffectiveCartier := hD ▸ D.property
    obtain ⟨f, _hf, hgen⟩ := hcartier.exists_regular_stalkIdeal_generator x
    exact ⟨f, hgen⟩
  choose f hf using hprincipal
  obtain ⟨_hregular, s, hs, _hequation⟩ := rationalSectionPadicPoint_parameters p b
  obtain ⟨d, r, t, hrpos, hr, ht, hboundary⟩ := hNC.2
  have hprod : Ideal.span {∏ a ∈ A, f a} =
      Ideal.span {Scheme.initialParameterProduct t r hr} := by
    rw [rationalSectionPadicDivisor_ideal, comap_finset_prod,
      Scheme.IdealSheafData.stalkIdeal_finset_prod] at hboundary
    have hfprod : (∏ a ∈ A, (I a).stalkIdeal x) = Ideal.span {∏ a ∈ A, f a} := by
      calc
        (∏ a ∈ A, (I a).stalkIdeal x) = ∏ a ∈ A, Ideal.span {f a} :=
          Finset.prod_congr rfl (fun a _ => hf a)
        _ = Ideal.span {∏ a ∈ A, f a} := Ideal.prod_span_singleton A f
    exact hfprod.symm.trans hboundary
  apply (Finset.card_le_card (show A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b) ⊆
      A.filter (fun a => ¬IsUnit (f a)) from ?_)).trans
    (nonunit_filter_card_le_two_of_parameter_product A f s hs d r t hrpos hr ht hprod)
  intro a ha
  obtain ⟨haA, haDiv⟩ := Finset.mem_filter.mp ha
  refine Finset.mem_filter.mpr ⟨haA, ?_⟩
  intro hunit
  have htop : (I a).stalkIdeal x = ⊤ :=
    (hf a).trans (Ideal.span_singleton_eq_top.mpr hunit)
  exact ((rationalSection_padic_stalkIdeal_eq_top_iff p a b).mp htop) haDiv

/-- Every distinct incident section has valuation-one intersection with the
selected section in a strictly normal-crossing p-adic family. -/
theorem rationalSectionPadicDivisor_padicVal_eq_one_of_isStrictNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a b : Projectivization ℚ (ℚ × ℚ)) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hdiv : (p : ℤ) ∣ rationalPointDelta a b)
    (hNC : (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt
        (rationalSectionPadicPoint p b)) :
    padicValInt p (rationalPointDelta a b) = 1 := by
  classical
  let S : Finset (Projectivization ℚ (ℚ × ℚ)) :=
    A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b)
  have haS : a ∈ S := Finset.mem_filter.mpr ⟨ha, hdiv⟩
  have hbS : b ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    rw [rationalPointDelta_self]
    exact dvd_zero (p : ℤ)
  have hcard := rationalSectionPadicDivisor_card_le_two_of_isStrictNormalCrossingsAt p A b hNC
  have hother : ∀ c ∈ A, c ≠ a → c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b := by
    intro c hc hca hcb hcdiv
    have hcS : c ∈ S := Finset.mem_filter.mpr ⟨hc, hcdiv⟩
    exact (not_lt_of_ge hcard) (Finset.two_lt_card_iff.mpr
      ⟨a, b, c, haS, hbS, hcS, hab, Ne.symm hca, Ne.symm hcb⟩)
  have hstalk := rationalSectionPadicDivisor_stalkIdeal_eq_pair_of_other_disjoint
    p A a b ha hb hab hother
  apply (rationalSectionPair_padic_isStrictNormalCrossingsAt_iff p a b hab hdiv).mp
  obtain ⟨hregular, d, r, t, hrpos, hr, ht, hideal⟩ := hNC
  exact ⟨hregular, d, r, t, hrpos, hr, ht, hstalk.symm.trans hideal⟩

/-- The determinant incidence and valuation conditions give strict normal
crossings for the actual finite p-adic divisor at the selected section point. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossingsAt_of_card_le_two
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A)
    (hcard : (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2)
    (hval : ∀ a ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
      padicValInt p (rationalPointDelta a b) = 1) :
    (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt
        (rationalSectionPadicPoint p b) := by
  classical
  let S : Finset (Projectivization ℚ (ℚ × ℚ)) :=
    A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b)
  have hbS : b ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    rw [rationalPointDelta_self]
    exact dvd_zero (p : ℤ)
  by_cases hsecond : ∃ a ∈ S, a ≠ b
  · obtain ⟨a, haS, hab⟩ := hsecond
    have ha : a ∈ A := (Finset.mem_filter.mp haS).1
    have hpab : (p : ℤ) ∣ rationalPointDelta a b := (Finset.mem_filter.mp haS).2
    have hother : ∀ c ∈ A, c ≠ a → c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b := by
      intro c hc hca hcb hpdiv
      have hcS : c ∈ S := Finset.mem_filter.mpr ⟨hc, hpdiv⟩
      exact (not_lt_of_ge hcard) (Finset.two_lt_card_iff.mpr
        ⟨a, b, c, haS, hbS, hcS, hab, Ne.symm hca, Ne.symm hcb⟩)
    have hstalk := rationalSectionPadicDivisor_stalkIdeal_eq_pair_of_other_disjoint
      p A a b ha hb hab hother
    obtain ⟨hregular, d, r, t, hrpos, hrd, hparameters, hideal⟩ :=
      (rationalSectionPair_padic_isStrictNormalCrossingsAt_iff p a b hab hpab).mpr
        (hval a ha hab hpab)
    exact ⟨hregular, d, r, t, hrpos, hrd, hparameters, hstalk.trans hideal⟩
  · have hother : ∀ c ∈ A, c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b := by
      intro c hc hcb hpdiv
      exact hsecond ⟨c, Finset.mem_filter.mpr ⟨hc, hpdiv⟩, hcb⟩
    have hstalk := rationalSectionPadicDivisor_stalkIdeal_eq_single_of_other_disjoint
      p A b hb hother
    obtain ⟨hregular, d, r, t, hrpos, hrd, hparameters, hideal⟩ :=
      rationalSection_padic_isStrictNormalCrossingsAt p b
    exact ⟨hregular, d, r, t, hrpos, hrd, hparameters, hstalk.trans hideal⟩

/-- The exact local arithmetic criterion for the actual p-adic finite family:
at most two original sections meet, and every distinct incident section has
valuation-one determinant with the selected section. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossingsAt_iff
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
    (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt
        (rationalSectionPadicPoint p b) ↔
      (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2 ∧
        ∀ a ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
          padicValInt p (rationalPointDelta a b) = 1 := by
  constructor
  · intro hNC
    refine ⟨rationalSectionPadicDivisor_card_le_two_of_isStrictNormalCrossingsAt p A b hNC, ?_⟩
    intro a ha hab hdiv
    exact rationalSectionPadicDivisor_padicVal_eq_one_of_isStrictNormalCrossingsAt
      p A a b ha hb hab hdiv hNC
  · rintro ⟨hcard, hval⟩
    exact rationalSectionPadicDivisor_isStrictNormalCrossingsAt_of_card_le_two
      p A b hb hcard hval

/-- The original integer family and its actual p-adic Cartier pullback have
identical strict normal-crossing behaviour at corresponding selected section points. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossingsAt_iff_integer
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
    (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt
        (rationalSectionPadicPoint p b) ↔
    (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p)) :=
  (rationalSectionPadicDivisor_isStrictNormalCrossingsAt_iff p A b hb).trans
    (rationalSectionFamily_isStrictNormalCrossingsAt_iff p A b hb).symm

end ShimizuYamaguchi26BranchedCoverings

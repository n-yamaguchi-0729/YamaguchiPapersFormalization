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
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicNormalCrossingsNecessity
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FullSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionIntersectionMultiplicity
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SingleSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.Algebraize

/-!
# Ordinary normal crossings for the actual p-adic finite section divisor

An etale neighbourhood of an ordinary normal-crossing point gives a strict
parameter product. The selected section is still a parameter in its stalk,
and the second incident section remains a nonunit. In dimension two these
two equations generate the maximal ideal. Faithful flatness descends this
identity to the original projective stalk, whose actual intersection length
is already known to be the determinant valuation.

This proves the ordinary normal-crossing criterion in Lemma 2.3 of Ryoji
Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1). The two implications compare the actual
global divisor; no openness assertion for an arbitrary pointwise strict
normal-crossing predicate is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma ideal_eq_maximalIdeal_of_flat_local_map
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat)
    (I : Ideal R) (hmap : I.map φ = IsLocalRing.maximalIdeal S) :
    I = IsLocalRing.maximalIdeal R := by
  algebraize [φ]
  let : Module.Flat R S := hflat
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcontract : (I.map φ).comap φ = I :=
    Ideal.comap_map_eq_self_of_faithfullyFlat I
  exact hcontract.symm.trans ((congrArg (Ideal.comap φ) hmap).trans
    (IsLocalRing.maximalIdeal_comap φ))

/-- Ordinary normal crossings force valuation one for each distinct section
meeting the selected section's actual closed p-adic point. -/
theorem rationalSectionPadicDivisor_padicVal_eq_one_of_isNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a b : Projectivization ℚ (ℚ × ℚ)) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hdiv : (p : ℤ) ∣ rationalPointDelta a b)
    (hNC : (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsNormalCrossingsAt
        (rationalSectionPadicPoint p b)) :
    padicValInt p (rationalPointDelta a b) = 1 := by
  classical
  let X : Scheme := ProjectiveLine ℤ_[p]
  let D : X.IdealSheafData := rationalSectionPadicDivisor p A
  let Ia : X.IdealSheafData := (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let Ib : X.IdealSheafData := (rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let x : X := rationalSectionPadicPoint p b
  have hcard := rationalSectionPadicDivisor_card_le_two_of_isNormalCrossingsAt p A b hb hNC
  have haS : a ∈ A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b) :=
    Finset.mem_filter.mpr ⟨ha, hdiv⟩
  have hbS : b ∈ A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b) := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    rw [rationalPointDelta_self]
    exact dvd_zero (p : ℤ)
  have hother : ∀ c ∈ A, c ≠ a → c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b := by
    intro c hc hca hcb hcdiv
    have hcS : c ∈ A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b) :=
      Finset.mem_filter.mpr ⟨hc, hcdiv⟩
    exact (not_lt_of_ge hcard) (Finset.two_lt_card_iff.mpr
      ⟨a, b, c, haS, hbS, hcS, hab, Ne.symm hca, Ne.symm hcb⟩)
  have hDpair : D.stalkIdeal x = Ia.stalkIdeal x * Ib.stalkIdeal x := by
    have h := rationalSectionPadicDivisor_stalkIdeal_eq_pair_of_other_disjoint
      p A a b ha hb hab hother
    rw [comap_mul, Scheme.IdealSheafData.stalkIdeal_mul] at h
    exact h
  have hx : x ∈ D.support :=
    (rationalSectionPadicDivisor_mem_support_iff p A b).mpr ⟨a, ha, hdiv⟩
  obtain ⟨Y, f, y, hetale, hpoint, hstrict⟩ := hNC
  have : Etale f := hetale
  have hy : y ∈ (D.comap f).support :=
    (mem_support_iff_of_comap_eq D (D.comap f) f y x hpoint rfl).mp hx
  obtain ⟨hregular, d, r, t, hrpos, hr, ht, hboundary⟩ := hstrict y hy
  let R : Type := X.presheaf.stalk (f y)
  let S : Type := Y.presheaf.stalk y
  let φ : R →+* S := (f.stalkMap y).hom
  have : IsRegularLocalRing S := hregular
  have : IsDomain S := IsRegularLocalRing.isDomain S
  have hparameters : ∃ s : Fin 2 → R, Scheme.IsRegularSystemOfParameters s ∧
      Ib.stalkIdeal (f y) = Ideal.span {s 0} := by
    have hsource : ∃ s : Fin 2 → X.presheaf.stalk x,
        Scheme.IsRegularSystemOfParameters s ∧ Ib.stalkIdeal x = Ideal.span {s 0} := by
      obtain ⟨_hregular, s, hs, hgen⟩ := rationalSectionPadicPoint_parameters p b
      exact ⟨s, hs, hgen⟩
    exact (congrArg (fun z : X => ∃ s : Fin 2 → X.presheaf.stalk z,
      Scheme.IsRegularSystemOfParameters s ∧ Ib.stalkIdeal z = Ideal.span {s 0}) hpoint).mpr hsource
  obtain ⟨s, hs, hIb⟩ := hparameters
  have hsmap : Scheme.IsRegularSystemOfParameters (fun i => φ (s i)) :=
    RingHom.isRegularSystemOfParameters_map_of_flat_of_formallyUnramified_of_essFiniteType
      φ (Flat.stalkMap f y) (FormallyUnramified.stalkMap f y)
      (LocallyOfFiniteType.stalkMap f y) s hs
  have hprime : Prime (φ (s 0)) :=
    EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem hsmap.1 hsmap.2
      (List.mem_ofFn.mpr ⟨0, rfl⟩)
  have hprincipal : ∃ ga : R, Ia.stalkIdeal (f y) = Ideal.span {ga} := by
    let Da : Scheme.EffectiveCartierDivisor X := rationalSectionPadicDivisor p {a}
    have hDa : (Da : X.IdealSheafData) = Ia := by
      rw [rationalSectionPadicDivisor_ideal, Finset.prod_singleton]
    obtain ⟨ga, _hga, hgen⟩ := Da.property.exists_regular_stalkIdeal_generator (f y)
    exact ⟨ga, (congrArg (fun J : X.IdealSheafData => J.stalkIdeal (f y)) hDa).symm.trans hgen⟩
  obtain ⟨ga, hIa⟩ := hprincipal
  have hnonunit : ¬IsUnit (φ ga) := by
    intro hunit
    have hsourceUnit : IsUnit ga := isUnit_of_map_unit φ ga hunit
    have htopAtImage : Ia.stalkIdeal (f y) = ⊤ :=
      hIa.trans (Ideal.span_singleton_eq_top.mpr hsourceUnit)
    have htop : Ia.stalkIdeal x = ⊤ :=
      (congrArg (fun z : X => Ia.stalkIdeal z = ⊤) hpoint).mp htopAtImage
    exact ((rationalSection_padic_stalkIdeal_eq_top_iff p a b).mp htop) hdiv
  have hDpairImage : D.stalkIdeal (f y) =
      Ia.stalkIdeal (f y) * Ib.stalkIdeal (f y) :=
    (congrArg (fun z : X => D.stalkIdeal z = Ia.stalkIdeal z * Ib.stalkIdeal z)
      hpoint).mpr hDpair
  have hDgen : D.stalkIdeal (f y) = Ideal.span {s 0 * ga} := by
    rw [hDpairImage, hIa, hIb, Ideal.span_singleton_mul_span_singleton, mul_comm ga (s 0)]
  have hprod : Ideal.span {φ (s 0) * φ ga} =
      Ideal.span {Scheme.initialParameterProduct t r hr} := by
    have hmap : (D.stalkIdeal (f y)).map φ = Ideal.span {φ (s 0) * φ ga} := by
      rw [hDgen, Ideal.map_span, Set.image_singleton, map_mul]
    exact hmap.symm.trans ((Scheme.IdealSheafData.stalkIdeal_comap D f y).symm.trans hboundary)
  have hmaxS : Ideal.span {φ (s 0), φ ga} = IsLocalRing.maximalIdeal S :=
    span_pair_eq_maximalIdeal_of_prime_nonunit_parameter_product
      (φ (s 0)) (φ ga) hprime hnonunit (fun i => φ (s i)) hsmap d r t ht hrpos hr hprod
  have hmapPair : (Ia.stalkIdeal (f y) ⊔ Ib.stalkIdeal (f y)).map φ =
      IsLocalRing.maximalIdeal S := by
    rw [hIa, hIb, ← Ideal.span_insert, Ideal.map_span, Set.image_pair]
    exact (congrArg Ideal.span (Set.pair_comm (φ ga) (φ (s 0)))).trans hmaxS
  have hmaxR : Ia.stalkIdeal (f y) ⊔ Ib.stalkIdeal (f y) = IsLocalRing.maximalIdeal R :=
    ideal_eq_maximalIdeal_of_flat_local_map φ (Flat.stalkMap f y) _ hmapPair
  have hmax : Ia.stalkIdeal x ⊔ Ib.stalkIdeal x = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (congrArg (fun z : X => Ia.stalkIdeal z ⊔ Ib.stalkIdeal z =
      IsLocalRing.maximalIdeal (X.presheaf.stalk z)) hpoint).mp hmaxR
  have hlength : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ia.stalkIdeal x ⊔ Ib.stalkIdeal x)) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]
    exact hmax
  have hval : (padicValInt p (rationalPointDelta a b) : ℕ∞) = 1 :=
    (rationalSectionPadicIntersection_length p a b hab).symm.trans hlength
  exact_mod_cast hval

/-- For the actual finite p-adic arrangement, ordinary and strict normal
crossings coincide. Necessity descends transverse intersection from the
supplied etale neighbourhood, and sufficiency uses the actual global strict
criterion, including generic support points. -/
theorem rationalSectionPadicDivisor_isNormalCrossings_iff_isStrictNormalCrossings
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A).IsNormalCrossings ↔
      (rationalSectionPadicDivisor p A).IsStrictNormalCrossings := by
  constructor
  · intro hNC
    have hselected (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
        (rationalSectionPadicDivisor p A :
          (ProjectiveLine ℤ_[p]).IdealSheafData).IsNormalCrossingsAt
            (rationalSectionPadicPoint p b) := by
      apply hNC
      apply (rationalSectionPadicDivisor_mem_support_iff p A b).mpr
      refine ⟨b, hb, ?_⟩
      rw [rationalPointDelta_self]
      exact dvd_zero (p : ℤ)
    apply (rationalSectionPadicDivisor_isStrictNormalCrossings_iff p A).mpr
    exact ⟨fun b hb => rationalSectionPadicDivisor_card_le_two_of_isNormalCrossingsAt
        p A b hb (hselected b hb),
      fun a ha b hb hab hdiv => rationalSectionPadicDivisor_padicVal_eq_one_of_isNormalCrossingsAt
        p A a b ha hb hab hdiv (hselected b hb)⟩
  · exact Scheme.IdealSheafData.IsStrictNormalCrossings.isNormalCrossings

end ShimizuYamaguchi26BranchedCoverings

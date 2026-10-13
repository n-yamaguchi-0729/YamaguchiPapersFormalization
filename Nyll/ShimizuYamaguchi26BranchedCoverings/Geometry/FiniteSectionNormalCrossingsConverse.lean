/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.SubschemeStalk
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerSectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCartier
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot3IntersectionMultiplicity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs
import Lean.Elab.Tactic.Omega

/-!
# The incidence bound forced by finite-family normal crossings

An actual section ideal is locally principal. At a section point over a
prime, the ambient local ring has a concrete two-parameter system, transported
from the integral infinity chart. Three nonunit factors cannot divide a
product of two prime parameters. Applying this to the finite product of
section ideals bounds the number of incident sections by two.

Source: Ryoji Shimizu and Naganori Yamaguchi,
On branched coverings of the projective line over the integers,
https://arxiv.org/abs/2608.15057v1, Lemma 2.3.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

private theorem nonunit_mul_not_dvd_prime
    {R : Type*} [CommRing R] [IsDomain R]
    {x y q : R} (hx : ¬IsUnit x) (hy : ¬IsUnit y) (hq : Prime q) :
    ¬x * y ∣ q := by
  intro h
  rcases hq.irreducible.dvd_iff.mp h with hu | ha
  · exact hx ((IsUnit.mul_iff.mp hu).1)
  · rcases prime_mul_iff.mp (ha.prime hq) with hxy | hxy
    · exact hy hxy.2
    · exact hx hxy.1

private theorem nonunit_triple_not_dvd_prime_mul
    {R : Type*} [CommRing R] [IsDomain R]
    {x y z s t : R} (hx : ¬IsUnit x) (hy : ¬IsUnit y) (hz : ¬IsUnit z)
    (hs : Prime s) (ht : Prime t) : ¬x * y * z ∣ s * t := by
  rintro ⟨w, hw⟩
  have hsdiv : s ∣ x * y * z * w := hw ▸ dvd_mul_right s t
  rcases hs.dvd_or_dvd hsdiv with hxyz | hwdiv
  · rcases hs.dvd_or_dvd hxyz with hxy | hzdiv
    · rcases hs.dvd_or_dvd hxy with hxdiv | hydiv
      · obtain ⟨x', rfl⟩ := hxdiv
        have htEq : t = y * z * (x' * w) := by
          apply mul_left_cancel₀ hs.ne_zero
          calc
            s * t = (s * x') * y * z * w := hw
            _ = s * (y * z * (x' * w)) := by ac_rfl
        exact nonunit_mul_not_dvd_prime hy hz ht ⟨x' * w, htEq⟩
      · obtain ⟨y', rfl⟩ := hydiv
        have htEq : t = x * z * (y' * w) := by
          apply mul_left_cancel₀ hs.ne_zero
          calc
            s * t = x * (s * y') * z * w := hw
            _ = s * (x * z * (y' * w)) := by ac_rfl
        exact nonunit_mul_not_dvd_prime hx hz ht ⟨y' * w, htEq⟩
    · obtain ⟨z', rfl⟩ := hzdiv
      have htEq : t = x * y * (z' * w) := by
        apply mul_left_cancel₀ hs.ne_zero
        calc
          s * t = x * y * (s * z') * w := hw
          _ = s * (x * y * (z' * w)) := by ac_rfl
      exact nonunit_mul_not_dvd_prime hx hy ht ⟨z' * w, htEq⟩
  · obtain ⟨w', rfl⟩ := hwdiv
    have htEq : t = x * y * (z * w') := by
      apply mul_left_cancel₀ hs.ne_zero
      calc
        s * t = x * y * z * (s * w') := hw
        _ = s * (x * y * (z * w')) := by ac_rfl
    exact nonunit_mul_not_dvd_prime hx hy ht ⟨z * w', htEq⟩

private theorem nonunit_filter_card_le_two_of_prod_dvd
    {R ι : Type*} [CommRing R] [IsDomain R]
    (A : Finset ι) (f : ι → R) [DecidablePred (fun a => ¬IsUnit (f a))]
    (s t : R) (hs : Prime s) (ht : Prime t)
    (hprod : (∏ a ∈ A, f a) ∣ s * t) :
    (A.filter (fun a => ¬IsUnit (f a))).card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge hcard)
  have hsub : ({a, b, c} : Finset ι) ⊆ A := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact (Finset.mem_filter.mp ha).1
    · exact (Finset.mem_filter.mp hb).1
    · exact (Finset.mem_filter.mp hc).1
  have hdiv := (Finset.prod_dvd_prod_of_subset {a, b, c} A f hsub).trans hprod
  have haNot : a ∉ ({b, c} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac⟩
  have hbNot : b ∉ ({c} : Finset ι) := by
    simpa only [Finset.mem_singleton] using hbc
  rw [Finset.prod_insert haNot, Finset.prod_insert hbNot, Finset.prod_singleton,
    ← mul_assoc] at hdiv
  exact nonunit_triple_not_dvd_prime_mul
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    (Finset.mem_filter.mp hc).2 hs ht hdiv

/-- In a regular local domain with an actual two-parameter system, a finite
product that generates an initial parameter product has at most two nonunit
factors. This ring-level argument is shared by the integer and p-adic fibres. -/
theorem nonunit_filter_card_le_two_of_parameter_product
    {R ι : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Finset ι) (f : ι → R) [DecidablePred (fun a => ¬IsUnit (f a))]
    (s : Fin 2 → R) (hs : Scheme.IsRegularSystemOfParameters s)
    (d r : ℕ) (t : Fin d → R) (hrpos : 0 < r) (hr : r ≤ d)
    (ht : Scheme.IsRegularSystemOfParameters t)
    (hprod : Ideal.span {∏ a ∈ A, f a} =
      Ideal.span {Scheme.initialParameterProduct t r hr}) :
    (A.filter (fun a => ¬IsUnit (f a))).card ≤ 2 := by
  have hd : d = 2 := by
    have hdim := EtaleFundamentalGroups.Kummer.regularSystem_length_eq_ringKrullDim
      (List.ofFn t) ht.1 ht.2
    have hdim₂ := EtaleFundamentalGroups.Kummer.regularSystem_length_eq_ringKrullDim
      (List.ofFn s) hs.1 hs.2
    have heq : ((d : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa only [List.length_ofFn] using hdim.trans hdim₂.symm
    exact_mod_cast heq
  subst d
  have hdiv : (∏ a ∈ A, f a) ∣ t 0 * t 1 := by
    have h := (Ideal.span_singleton_eq_span_singleton.mp hprod).dvd
    apply h.trans
    rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
    · simpa only [Scheme.initialParameterProduct, Fin.prod_univ_one, Fin.castLE_zero] using
        dvd_mul_right (t 0) (t 1)
    · simpa only [Scheme.initialParameterProduct, Fin.castLE_rfl, id_eq,
        Fin.prod_univ_two] using (dvd_refl (t 0 * t 1))
  have htprime (i : Fin 2) : Prime (t i) :=
    EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem ht.1 ht.2
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact nonunit_filter_card_le_two_of_prod_dvd A f
    (t 0) (t 1) (htprime 0) (htprime 1) hdiv

private theorem rationalSectionPoint_has_two_parameters
    (p : ℕ) [hp : Fact p.Prime] (b : Projectivization ℚ (ℚ × ℚ)) :
    ∃ s : Fin 2 → (ProjectiveLine ℤ).presheaf.stalk
      (rationalSection b (integerPrimePoint p)), Scheme.IsRegularSystemOfParameters s := by
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  let e : ProjectiveLine ℤ ≅ ProjectiveLine ℤ := integralCoordinateChange
    (rationalPointNumerator b) (rationalPointDenominator b)
    hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec
  let y : ProjectiveLine ℤ := integerProjectiveInfinityPoint p
  let F : (ProjectiveLine ℤ).presheaf.stalk (e.inv y) ≃+*
      IntegerProjectiveInfinityLocalRing p :=
    (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  let g : ℤ[X] →+* IntegerProjectiveInfinityLocalRing p :=
    infinityChartGermAt ℤ (integerInfinityChartPoint p)
  let t : Fin 2 → IntegerProjectiveInfinityLocalRing p :=
    ![g Polynomial.X, g (Polynomial.C (p : ℤ) - Polynomial.C 1 * Polynomial.X)]
  have ht : Scheme.IsRegularSystemOfParameters t :=
    integerProjectiveInfinitySection_isRegularSystemOfParameters p 1 p
      (Int.natCast_ne_zero.mpr hp.out.ne_zero) padicValInt_self
  have hpoint : rationalSection b (integerPrimePoint p) = e.inv y :=
    integralSection_at_integerPrimePoint (rationalPointNumerator b)
      (rationalPointDenominator b) hb.choose hb.choose_spec.choose
      hb.choose_spec.choose_spec p
  rw [hpoint]
  exact ⟨F.symm ∘ t, ht.map_ringEquiv F.symm⟩

private theorem rationalSection_stalkIdeal_ne_top_of_dvd
    (p : ℕ) [hp : Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ))
    (hdiv : (p : ℤ) ∣ rationalPointDelta a b) :
    (rationalSection a).ker.stalkIdeal (rationalSection b (integerPrimePoint p)) ≠ ⊤ := by
  by_cases hab : a = b
  · subst a
    let q : Spec (CommRingCat.of ℤ) := integerPrimePoint p
    change (rationalSection b).ker.stalkIdeal (rationalSection b q) ≠ ⊤
    rw [← (rationalSection b).ker_stalkMap_eq_stalkIdeal q]
    exact RingHom.ker_ne_top ((rationalSection b).stalkMap q).hom
  · intro htop
    have hlength := rationalSectionIntersection_length p a b hab
    have hlengthZero : Module.length
        ((ProjectiveLine ℤ).presheaf.stalk (rationalSection b (integerPrimePoint p)))
        ((ProjectiveLine ℤ).presheaf.stalk (rationalSection b (integerPrimePoint p)) ⧸
          rationalSectionIntersectionIdeal a b (rationalSection b (integerPrimePoint p))) = 0 := by
      rw [rationalSectionIntersectionIdeal, htop, top_sup_eq]
      exact Module.length_eq_zero_iff.mpr (Ideal.Quotient.subsingleton_iff.mpr rfl)
    have hval : padicValInt p (rationalPointDelta a b) = 0 := by
      exact_mod_cast hlength.symm.trans hlengthZero
    have hdelta : rationalPointDelta a b ≠ 0 := by
      rw [rationalPointDelta_eq_signed_coordinateDeterminant]
      split_ifs
      · exact neg_ne_zero.mpr (rationalPoint_coordinateDeterminant_ne_zero a b hab)
      · exact rationalPoint_coordinateDeterminant_ne_zero a b hab
    rcases padicValInt.eq_zero_iff.mp hval with hp1 | hzero | hnot
    · exact hp.out.ne_one hp1
    · exact hdelta hzero
    · exact hnot hdiv

/-- Strict normal crossings of the actual finite section product force at
most two original sections to pass through the selected point over `p`. -/
theorem rationalSectionFamily_card_le_two_of_isStrictNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ))
    (hNC : (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p))) :
    (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2 := by
  classical
  let x : ProjectiveLine ℤ := rationalSection b (integerPrimePoint p)
  let R : Type := (ProjectiveLine ℤ).presheaf.stalk x
  have : IsRegularLocalRing R := hNC.1
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hprincipal (a : Projectivization ℚ (ℚ × ℚ)) :
      ∃ f : R, (rationalSection a).ker.stalkIdeal x = Ideal.span {f} := by
    obtain ⟨U, hx, f, _hf, hgen⟩ := rationalSection_ker_isEffectiveCartier a x
    refine ⟨(ProjectiveLine ℤ).presheaf.germ U.1 x hx f, ?_⟩
    rw [Scheme.IdealSheafData.stalkIdeal_eq_map_ideal _ x U hx,
      hgen, Ideal.map_span, Set.image_singleton]
  choose f hf using hprincipal
  obtain ⟨s, hs⟩ := rationalSectionPoint_has_two_parameters p b
  obtain ⟨d, r, t, hrpos, hr, ht, hboundary⟩ := hNC.2
  have hprod : Ideal.span {∏ a ∈ A, f a} =
      Ideal.span {Scheme.initialParameterProduct t r hr} := by
    rw [Scheme.IdealSheafData.stalkIdeal_finset_prod] at hboundary
    have hfprod : (∏ a ∈ A, (rationalSection a).ker.stalkIdeal x) =
        Ideal.span {∏ a ∈ A, f a} := by
      calc
        (∏ a ∈ A, (rationalSection a).ker.stalkIdeal x) = ∏ a ∈ A, Ideal.span {f a} :=
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
  apply rationalSection_stalkIdeal_ne_top_of_dvd p a b haDiv
  exact (hf a).trans (Ideal.span_singleton_eq_top.mpr hunit)

/-- Every pair of distinct incident sections in a strictly normal-crossing
finite family has determinant valuation one. The incidence bound removes
all other factors from the actual stalk before applying the pair converse. -/
theorem rationalSectionFamily_padicVal_eq_one_of_isStrictNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a b : Projectivization ℚ (ℚ × ℚ)) (ha : a ∈ A) (hb : b ∈ A)
    (hab : a ≠ b) (hdiv : (p : ℤ) ∣ rationalPointDelta a b)
    (hNC : (∏ c ∈ A, (rationalSection c).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p))) :
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
  have hpair : ({a, b} : Finset (Projectivization ℚ (ℚ × ℚ))) = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact haS
      · exact hbS
    · rw [Finset.card_pair hab]
      exact rationalSectionFamily_card_le_two_of_isStrictNormalCrossingsAt p A b hNC
  have hother : ∀ c ∈ A, c ≠ a → c ≠ b → ¬(p : ℤ) ∣ rationalPointDelta c b := by
    intro c hc hca hcb hcdiv
    have hcS : c ∈ S := Finset.mem_filter.mpr ⟨hc, hcdiv⟩
    rw [← hpair] at hcS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcS
    exact hcS.elim hca hcb
  have hstalk := rationalSectionFamily_stalkIdeal_eq_pair_of_other_disjoint
    p A a b ha hb hab hother
  apply rationalSectionPair_padicVal_eq_one_of_isStrictNormalCrossingsAt p a b hab hdiv
  obtain ⟨hregular, d, r, t, hrpos, hr, ht, hideal⟩ := hNC
  exact ⟨hregular, d, r, t, hrpos, hr, ht, hstalk.symm.trans hideal⟩

/-- The exact arithmetic criterion at a selected section point: the finite
union is strictly normal crossing precisely when at most two sections meet
there and every distinct incident pair has determinant valuation one. -/
theorem rationalSectionFamily_isStrictNormalCrossingsAt_iff
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
    (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt
        (rationalSection b (integerPrimePoint p)) ↔
      (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2 ∧
        ∀ a ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
          padicValInt p (rationalPointDelta a b) = 1 := by
  constructor
  · intro hNC
    refine ⟨rationalSectionFamily_card_le_two_of_isStrictNormalCrossingsAt p A b hNC, ?_⟩
    intro a ha hab hdiv
    exact rationalSectionFamily_padicVal_eq_one_of_isStrictNormalCrossingsAt
      p A a b ha hb hab hdiv hNC
  · rintro ⟨hcard, hval⟩
    exact rationalSectionFamily_isStrictNormalCrossingsAt_of_card_le_two p A b hb hcard hval

end ShimizuYamaguchi26BranchedCoverings

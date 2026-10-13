/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SpecialFiberIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot4DyadicCollision
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Closure
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.Closeds
import Lean.Elab.Tactic.Omega

/-!
# Normal crossings along an integral special fibre

The selected-section criterion gives the arithmetic criterion at every
support point of the actual finite union over a prime. It is enough to
check closed points: each selected section point is closed, and the
existing sufficient criterion covers every point over that prime.

At two, the actual special-fibre collision theorem rules out three
incident sections unless some pair has determinant valuation at least
two. Consequently failure of strict normal crossings on the integral
fibre is equivalent to the existence of such a pair in the original family.
No comparison with normal crossings after base change to the p-adic
integers is asserted here.

Source: Ryoji Shimizu and Naganori Yamaguchi,
On branched coverings of the projective line over the integers,
https://arxiv.org/abs/2608.15057v1, Lemmas 2.3 and 2.4.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

private theorem rationalSectionPoint_mem_family_support
    (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A)
    (q : Spec (CommRingCat.of ℤ)) :
    rationalSection b q ∈ (∏ a ∈ A, (rationalSection a).ker).support := by
  rw [Scheme.IdealSheafData.support_finset_prod]
  apply (Finset.le_sup (f := fun a : Projectivization ℚ (ℚ × ℚ) =>
    (rationalSection a).ker.support) hb)
  change rationalSection b q ∈ ((rationalSection b).ker.support : Set (ProjectiveLine ℤ))
  rw [Scheme.Hom.support_ker]
  exact subset_closure ⟨q, rfl⟩

private theorem rationalSectionPoint_base
    (b : Projectivization ℚ (ℚ × ℚ)) (q : Spec (CommRingCat.of ℤ)) :
    ProjSpace.π ℤ 1 (rationalSection b q) = q := by
  rw [← Scheme.Hom.comp_apply, rationalSection_comp_π]
  exact CategoryTheory.id_apply (X := (Spec (CommRingCat.of ℤ)).carrier) q

private theorem rationalSectionPoint_isClosed
    (p : ℕ) [Fact p.Prime] (b : Projectivization ℚ (ℚ × ℚ)) :
    IsClosed ({rationalSection b (integerPrimePoint p)} : Set (ProjectiveLine ℤ)) := by
  have hq : IsClosed ({integerPrimePoint p} : Set (Spec (CommRingCat.of ℤ))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (integerPrimePoint p)).mpr
      (Int.ideal_span_isMaximal_of_prime p)
  have h := (rationalSection b).isClosedEmbedding.isClosedMap
    ({integerPrimePoint p} : Set (Spec (CommRingCat.of ℤ))) hq
  have himage : (fun q : Spec (CommRingCat.of ℤ) => rationalSection b q) ''
      {integerPrimePoint p} = {rationalSection b (integerPrimePoint p)} :=
    Set.image_singleton
  exact himage ▸ h

/-- The arithmetic criterion holds simultaneously at all points of the
actual integral boundary over the chosen prime. -/
theorem rationalSectionFamily_isStrictNormalCrossings_over_prime_iff
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∀ x : ProjectiveLine ℤ, x ∈ (∏ a ∈ A, (rationalSection a).ker).support →
      ProjSpace.π ℤ 1 x = integerPrimePoint p →
        (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt x) ↔
      (∀ b ∈ A, (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2) ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
          padicValInt p (rationalPointDelta a b) = 1) := by
  constructor
  · intro hNC
    have hselected (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
        (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt
          (rationalSection b (integerPrimePoint p)) :=
      hNC _ (rationalSectionPoint_mem_family_support A b hb (integerPrimePoint p))
        (rationalSectionPoint_base b (integerPrimePoint p))
    refine ⟨fun b hb =>
      rationalSectionFamily_card_le_two_of_isStrictNormalCrossingsAt p A b (hselected b hb), ?_⟩
    intro a ha b hb hab hdiv
    exact rationalSectionFamily_padicVal_eq_one_of_isStrictNormalCrossingsAt
      p A a b ha hb hab hdiv (hselected b hb)
  · rintro ⟨hcard, hval⟩ x hx hbase
    exact rationalSectionFamily_isStrictNormalCrossingsAt_over_prime p A hcard hval x hx hbase

/-- Checking closed points of the integral boundary over a prime suffices
to check the entire boundary over that prime. -/
theorem rationalSectionFamily_isStrictNormalCrossings_over_prime_iff_closed
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∀ x : ProjectiveLine ℤ, x ∈ (∏ a ∈ A, (rationalSection a).ker).support →
      ProjSpace.π ℤ 1 x = integerPrimePoint p →
        (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt x) ↔
      (∀ x : ProjectiveLine ℤ, x ∈ (∏ a ∈ A, (rationalSection a).ker).support →
        ProjSpace.π ℤ 1 x = integerPrimePoint p →
          IsClosed ({x} : Set (ProjectiveLine ℤ)) →
            (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt x) := by
  constructor
  · intro h x hx hbase _hclosed
    exact h x hx hbase
  · intro h
    apply (rationalSectionFamily_isStrictNormalCrossings_over_prime_iff p A).mpr
    have hselected (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
        (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt
          (rationalSection b (integerPrimePoint p)) :=
      h _ (rationalSectionPoint_mem_family_support A b hb (integerPrimePoint p))
        (rationalSectionPoint_base b (integerPrimePoint p)) (rationalSectionPoint_isClosed p b)
    refine ⟨fun b hb =>
      rationalSectionFamily_card_le_two_of_isStrictNormalCrossingsAt p A b (hselected b hb), ?_⟩
    intro a ha b hb hab hdiv
    exact rationalSectionFamily_padicVal_eq_one_of_isStrictNormalCrossingsAt
      p A a b ha hb hab hdiv (hselected b hb)

private theorem exists_dyadic_pair_of_three_incident
    (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ))
    (hcard : 2 < (A.filter (fun a => (2 : ℤ) ∣ rationalPointDelta a b)).card) :
    ∃ a ∈ A, ∃ c ∈ A, a ≠ c ∧ 2 ≤ padicValInt 2 (rationalPointDelta a c) := by
  classical
  let S : Finset (Projectivization ℚ (ℚ × ℚ)) :=
    A.filter (fun a => (2 : ℤ) ∣ rationalPointDelta a b)
  obtain ⟨f, hf⟩ : ∃ f : Fin 3 ↪ Projectivization ℚ (ℚ × ℚ), Set.range f ⊆ S :=
    Function.Embedding.exists_of_card_le_finset (by
      rw [Fintype.card_fin]
      exact hcard)
  have hfS (i : Fin 3) : f i ∈ S := hf ⟨i, rfl⟩
  apply exists_two_le_padicValInt_delta_in_boundary A f f.injective
    (fun i => (Finset.mem_filter.mp (hfS i)).1) (rationalSectionSpecialFiberPoint 2 b)
  intro i
  apply (rationalSectionSpecialFiberPoint_mem_iff 2 b (f i)).mpr
  have hdiv : (2 : ℤ) ∣ rationalPointDelta (f i) b := (Finset.mem_filter.mp (hfS i)).2
  rw [rationalPointDelta_dvd_iff, coordinateDeterminant_swap]
  exact Int.dvd_neg.mpr ((rationalPointDelta_dvd_iff 2 (f i) b).mp hdiv)

/-- On the integral fibre over two, failure of strict normal crossings
is exactly the existence of a pair of distinct original sections whose
intersection determinant has dyadic valuation at least two. -/
theorem rationalSectionFamily_not_isStrictNormalCrossings_over_two_iff
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (¬ ∀ x : ProjectiveLine ℤ, x ∈ (∏ a ∈ A, (rationalSection a).ker).support →
      ProjSpace.π ℤ 1 x = integerPrimePoint 2 →
        (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt x) ↔
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ 2 ≤ padicValInt 2 (rationalPointDelta a b) := by
  classical
  constructor
  · intro hnot
    by_contra hpair
    apply hnot
    apply (rationalSectionFamily_isStrictNormalCrossings_over_prime_iff 2 A).mpr
    constructor
    · intro b _hb
      by_contra hcard
      exact hpair (exists_dyadic_pair_of_three_incident A b (Nat.lt_of_not_ge hcard))
    · intro a ha b hb hab hdiv
      have hdet := rationalPoint_coordinateDeterminant_ne_zero a b hab
      have hpower : (2 : ℤ) ^ 1 ∣ coordinateDeterminant
          (rationalPointNumerator a) (rationalPointDenominator a)
          (rationalPointNumerator b) (rationalPointDenominator b) := by
        rw [pow_one]
        exact (rationalPointDelta_dvd_iff 2 a b).mp hdiv
      have hpositive : 1 ≤ padicValInt 2 (rationalPointDelta a b) := by
        rw [padicValInt_rationalPointDelta]
        exact ((padicValInt_dvd_iff 1 _).mp hpower).resolve_left hdet
      have hsmall : ¬2 ≤ padicValInt 2 (rationalPointDelta a b) :=
        fun hlarge => hpair ⟨a, ha, b, hb, hab, hlarge⟩
      omega
  · rintro ⟨a, ha, b, hb, hab, hlarge⟩ hNC
    have hdiv : (2 : ℤ) ∣ rationalPointDelta a b := by
      have hpower : (2 : ℤ) ^ 1 ∣ rationalPointDelta a b :=
        (padicValInt_dvd_iff (p := 2) 1 (rationalPointDelta a b)).mpr
          (Or.inr (by omega))
      simpa only [pow_one] using hpower
    have hone := (rationalSectionFamily_isStrictNormalCrossings_over_prime_iff 2 A).mp hNC
    have heq := hone.2 a ha b hb hab hdiv
    omega

end ShimizuYamaguchi26BranchedCoverings

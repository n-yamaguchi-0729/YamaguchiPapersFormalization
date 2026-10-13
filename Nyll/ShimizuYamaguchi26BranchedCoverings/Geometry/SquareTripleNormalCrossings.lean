/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.Normalization
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.AffineRationalSectionCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicNormalCrossingsComparison
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FullSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The geometric calculation in Example 2.8

For a prime `p`, the actual boundary determined by `{0,p^2,infinity}` has
ordinary normal crossings at precisely the other primes. The calculation
uses the canonical rational projective points and their actual p-adic Cartier
divisor. It makes no assertion about triviality of the complement's
fundamental group, which also requires the inertia and solvable-quotient
arguments in the paper.

Source: Ryoji Shimizu and Naganori Yamaguchi, Example 2.8 of
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1). Its geometric calculation holds also for
`p = 2`; the example's oddness restriction is needed in the fundamental-group
argument, which is separate from the result here.
-/

noncomputable section

open AlgebraicGeometry AnabelianGeometry.ProjectiveLine

namespace ShimizuYamaguchi26BranchedCoverings

/-- The three original rational boundary points in Example 2.8. -/
def squareTripleBoundary (p : ℕ) : Finset (Projectivization ℚ (ℚ × ℚ)) := by
  classical
  exact {affinePoint ((0 : ℤ) : ℚ), affinePoint (((p : ℤ) ^ 2 : ℤ) : ℚ), infinityPoint}

private theorem squareTriple_pairwise_not_dvd
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : q ≠ p)
    (a b : Projectivization ℚ (ℚ × ℚ))
    (ha : a ∈ squareTripleBoundary p) (hb : b ∈ squareTripleBoundary p) (hab : a ≠ b) :
    ¬ (q : ℤ) ∣ rationalPointDelta a b := by
  classical
  have hnotOne : ¬ (q : ℤ) ∣ (1 : ℤ) := by
    intro hdiv
    have hnat : q ∣ 1 := by exact_mod_cast hdiv
    exact hq.ne_one (Nat.dvd_one.mp hnat)
  have hnotSquare : ¬ (q : ℤ) ∣ (p : ℤ) ^ 2 := by
    intro hdiv
    have hnat : q ∣ p ^ 2 := by exact_mod_cast hdiv
    exact hpq ((hp.dvd_iff_eq hq.ne_one).mp (hq.dvd_of_dvd_pow hnat)).symm
  simp only [squareTripleBoundary, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · rw [rationalPointDelta_affine_int, zero_sub, Int.dvd_neg]
      exact hnotSquare
    · rw [rationalPointDelta_affine_int_infinity]
      exact hnotOne
  · rcases hb with rfl | rfl | rfl
    · rw [rationalPointDelta_affine_int, sub_zero]
      exact hnotSquare
    · exact (hab rfl).elim
    · rw [rationalPointDelta_affine_int_infinity]
      exact hnotOne
  · rcases hb with rfl | rfl | rfl
    · rw [rationalPointDelta_infinity_affine_int]
      exact hnotOne
    · rw [rationalPointDelta_infinity_affine_int]
      exact hnotOne
    · exact (hab rfl).elim

/-- Away from `p`, all three actual sections are disjoint in the special fibre,
so their entire actual p-adic boundary has strict normal crossings. -/
theorem squareTripleBoundary_isStrictNormalCrossings_of_ne
    (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : q ≠ p) :
    (rationalSectionPadicDivisor q (squareTripleBoundary p)).IsStrictNormalCrossings := by
  classical
  apply (rationalSectionPadicDivisor_isStrictNormalCrossings_iff q (squareTripleBoundary p)).mpr
  constructor
  · intro b hb
    have hsub : (squareTripleBoundary p).filter
        (fun a => (q : ℤ) ∣ rationalPointDelta a b) ⊆ {b} := by
      intro a ha
      obtain ⟨haA, hdiv⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_singleton.mpr
      by_contra hab
      exact squareTriple_pairwise_not_dvd p q hp.out hq.out hpq a b haA hb hab hdiv
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    omega
  · intro a ha b hb hab hdiv
    exact (squareTriple_pairwise_not_dvd p q hp.out hq.out hpq a b ha hb hab hdiv).elim

/-- At `p`, the two finite sections meet to order two, so the actual triple
fails ordinary normal crossings. -/
theorem squareTripleBoundary_not_isNormalCrossings
    (p : ℕ) [hp : Fact p.Prime] :
    ¬ (rationalSectionPadicDivisor p (squareTripleBoundary p)).IsNormalCrossings := by
  classical
  let a : Projectivization ℚ (ℚ × ℚ) := affinePoint ((0 : ℤ) : ℚ)
  let b : Projectivization ℚ (ℚ × ℚ) := affinePoint (((p : ℤ) ^ 2 : ℤ) : ℚ)
  have ha : a ∈ squareTripleBoundary p := Finset.mem_insert_self _ _
  have hb : b ∈ squareTripleBoundary p :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hab : a ≠ b := by
    intro heq
    have hcoords := congrArg rationalPointNumerator heq
    change rationalPointNumerator (affinePoint ((0 : ℤ) : ℚ)) =
      rationalPointNumerator (affinePoint (((p : ℤ) ^ 2 : ℤ) : ℚ)) at hcoords
    have hzero : (0 : ℤ) = (p : ℤ) ^ 2 := by
      simpa only [(rationalPointCoordinates_affine_int 0).1,
        (rationalPointCoordinates_affine_int ((p : ℤ) ^ 2)).1] using hcoords
    exact (pow_ne_zero 2 (Int.natCast_ne_zero.mpr hp.out.ne_zero)) hzero.symm
  have hdelta : rationalPointDelta a b = -((p : ℤ) ^ 2) := by
    exact (rationalPointDelta_affine_int 0 ((p : ℤ) ^ 2)).trans (zero_sub _)
  have hdiv : (p : ℤ) ∣ rationalPointDelta a b := by
    rw [hdelta, Int.dvd_neg, pow_two]
    exact dvd_mul_right (p : ℤ) (p : ℤ)
  intro hNC
  have hlocal : (rationalSectionPadicDivisor p (squareTripleBoundary p) :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsNormalCrossingsAt
        (rationalSectionPadicPoint p b) := by
    apply hNC
    exact (rationalSectionPadicDivisor_mem_support_iff p (squareTripleBoundary p) b).mpr
      ⟨a, ha, hdiv⟩
  have hval := rationalSectionPadicDivisor_padicVal_eq_one_of_isNormalCrossingsAt
    p (squareTripleBoundary p) a b ha hb hab hdiv hlocal
  rw [hdelta, padicValInt, Int.natAbs_neg, Int.natAbs_pow,
    Int.natAbs_natCast, padicValNat.prime_pow] at hval
  omega

/-- The exact set of bad primes in the geometric part of Example 2.8. -/
theorem squareTripleBoundary_isNormalCrossings_iff
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    (rationalSectionPadicDivisor q (squareTripleBoundary p)).IsNormalCrossings ↔ q ≠ p := by
  constructor
  · intro hNC hqp
    subst q
    exact squareTripleBoundary_not_isNormalCrossings p hNC
  · intro hqp
    exact (squareTripleBoundary_isStrictNormalCrossings_of_ne p q hqp).isNormalCrossings

end ShimizuYamaguchi26BranchedCoverings

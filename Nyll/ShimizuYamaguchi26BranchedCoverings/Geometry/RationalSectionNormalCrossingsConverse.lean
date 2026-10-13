/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Basic

/-!
# The normal-crossings converse for arbitrary rational sections

For two distinct rational points whose integral sections meet over `p`, strict
normal crossings of their actual product at the second section's point forces
valuation one of the paper's determinant. The integral Bezout coordinate change
sends that actual point to the integer infinity-chart point and transports both
kernel ideal sheaves to the normalized pair. Finite-etale pullback along this
isomorphism preserves strict normal crossings, so the established normalized
converse applies. The sign convention for `Delta` preserves both divisibility
and valuation.

Together with the existing forward implication this gives the two-section
criterion in Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ShimizuYamaguchi26BranchedCoverings

/-- If two distinct original rational sections meet over `p`, strict normal
crossings of their actual product at that intersection forces valuation one. -/
theorem rationalSectionPair_padicVal_eq_one_of_isStrictNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b)
    (hpdiv : (p : ℤ) ∣ rationalPointDelta a b)
    (hNC : ((rationalSection a).ker * (rationalSection b).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p))) :
    padicValInt p (rationalPointDelta a b) = 1 := by
  let ha : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  let e : ProjectiveLine ℤ ≅ ProjectiveLine ℤ := integralCoordinateChange
    (rationalPointNumerator b) (rationalPointDenominator b)
    hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec
  let y : ProjectiveLine ℤ := integerProjectiveInfinityPoint p
  let U : ℤ := -(hb.choose * rationalPointNumerator a +
    hb.choose_spec.choose * rationalPointDenominator a)
  let V : ℤ := coordinateDeterminant
    (rationalPointNumerator b) (rationalPointDenominator b)
    (rationalPointNumerator a) (rationalPointDenominator a)
  obtain ⟨A, B, hAB⟩ : IsCoprime U V :=
    isCoprime_normalizedCoordinates
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      hb.choose_spec.choose_spec ha
  let I : (ProjectiveLine ℤ).IdealSheafData :=
    (rationalSection a).ker * (rationalSection b).ker
  let J : (ProjectiveLine ℤ).IdealSheafData :=
    (integralSection 1 0 1 0 (by decide)).ker * (integralSection U V A B hAB).ker
  have hpull : I.comap e.inv = J :=
    integralSectionPair_ker_comap_coordinateChange_inv
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose A B
      ha.choose_spec.choose_spec hb.choose_spec.choose_spec hAB
  have hpoint : rationalSection b (integerPrimePoint p) = e.inv y :=
    integralSection_at_integerPrimePoint
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec p
  have : IsFiniteEtale e.inv := by constructor
  have hnormal : J.IsStrictNormalCrossingsAt y := by
    rw [← hpull]
    apply Scheme.IdealSheafData.IsStrictNormalCrossingsAt.comap_of_finiteEtale I e.inv y
    rw [← hpoint]
    exact hNC
  have hV : V ≠ 0 := rationalPoint_coordinateDeterminant_ne_zero b a (Ne.symm hab)
  have hpV : (p : ℤ) ∣ V := by
    dsimp only [V]
    rw [coordinateDeterminant_swap]
    exact Int.dvd_neg.mpr ((rationalPointDelta_dvd_iff p a b).mp hpdiv)
  have hval : padicValInt p V = 1 :=
    integralSectionPair_padicVal_eq_one_of_isStrictNormalCrossingsAt_infinity
      p U V A B hAB hV hpV hnormal
  rw [padicValInt_rationalPointDelta]
  dsimp only [V] at hval
  rw [coordinateDeterminant_swap] at hval
  simpa only [padicValInt, Int.natAbs_neg] using hval

/-- At the intersection of two distinct rational sections over `p`, their
actual product has strict normal crossings exactly when `Delta` has valuation one. -/
theorem rationalSectionPair_isStrictNormalCrossingsAt_iff
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b)
    (hpdiv : (p : ℤ) ∣ rationalPointDelta a b) :
    ((rationalSection a).ker * (rationalSection b).ker).IsStrictNormalCrossingsAt
        (rationalSection b (integerPrimePoint p)) ↔
      padicValInt p (rationalPointDelta a b) = 1 :=
  ⟨rationalSectionPair_padicVal_eq_one_of_isStrictNormalCrossingsAt p a b hab hpdiv,
    rationalSectionPair_isStrictNormalCrossingsAt p a b hab⟩

end ShimizuYamaguchi26BranchedCoverings

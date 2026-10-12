/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PrimitiveSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Intersection of the actual rational sections with the infinity section

The intersection ideal is the sum of the stalk ideals of the two actual
closed section morphisms. On the infinity chart these ideals are generated
by their primitive linear equations. If the second rational point is infinity,
the sum is exactly the two-equation ideal already calculated in the actual
integral projective stalk.

For distinct original rational points, one of them infinity, the resulting
local intersection length is `v_p(Δ)`. This is the infinity case of Lemma 2.3
of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
Transport to an arbitrary pair and the normal-crossing criterion remain
separate requirements of the full lemma.
-/

noncomputable section

open AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- The intersection ideal of the two actual rational sections in a projective stalk. -/
def rationalSectionIntersectionIdeal
    (a b : Projectivization ℚ (ℚ × ℚ)) (x : ProjectiveLine ℤ) :
    Ideal ((ProjectiveLine ℤ).presheaf.stalk x) :=
  (rationalSection a).ker.stalkIdeal x ⊔ (rationalSection b).ker.stalkIdeal x

private theorem rationalSection_stalkIdeal_eq
    (a : Projectivization ℚ (ℚ × ℚ)) (q : PrimeSpectrum ℤ[X]) :
    (rationalSection a).ker.stalkIdeal (infinityChartEmbedding ℤ q) =
      (infinitySectionIdeal (rationalPointNumerator a) (rationalPointDenominator a)).map
        (infinityChartGermAt ℤ q) := by
  unfold rationalSection
  exact integralSection_stalkIdeal_eq _ _ _ _ _ q

/-- At infinity, the actual section intersection ideal is the two-equation ideal in the
integral projective stalk; the statement also covers primes with empty intersection. -/
theorem rationalSectionIntersectionIdeal_at_infinity
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ))
    (hb : b.rep.2 = 0) :
    rationalSectionIntersectionIdeal a b (integerProjectiveInfinityPoint p) =
      integerProjectiveInfinityIntersectionIdeal p
        (rationalPointNumerator a) (rationalPointDenominator a) := by
  have hnum : rationalPointNumerator b = 1 := by
    rw [rationalPointNumerator, ite_eq_left hb]
  have hden : rationalPointDenominator b = 0 := by
    rw [rationalPointDenominator, ite_eq_left hb]
  simp only [rationalSectionIntersectionIdeal, integerProjectiveInfinityPoint,
    rationalSection_stalkIdeal_eq, hnum, hden]
  change (infinitySectionIdeal (rationalPointNumerator a) (rationalPointDenominator a)).map
        (infinityChartGermAt ℤ (integerInfinityChartPoint p)) ⊔
      (infinitySectionIdeal 1 0).map (infinityChartGermAt ℤ (integerInfinityChartPoint p)) =
    (infinityIntersectionIdeal (rationalPointNumerator a) (rationalPointDenominator a)).map
      (infinityChartGermAt ℤ (integerInfinityChartPoint p))
  simp only [infinitySectionIdeal, map_one, map_zero, one_mul, zero_sub,
    Ideal.span_singleton_neg, ← Ideal.map_sup]
  apply congrArg (fun I : Ideal ℤ[X] => I.map (infinityChartGermAt ℤ (integerInfinityChartPoint p)))
  rw [infinityIntersectionIdeal, Ideal.span_insert, sup_comm]

/-- The intersection multiplicity of the original rational sections, with the second point
at infinity, is the valuation of the paper's `Δ` at every prime. -/
theorem rationalSectionIntersection_length_at_infinity
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ))
    (hab : a ≠ b) (hb : b.rep.2 = 0) :
    Module.length (IntegerProjectiveInfinityLocalRing p)
        (IntegerProjectiveInfinityLocalRing p ⧸
          rationalSectionIntersectionIdeal a b (integerProjectiveInfinityPoint p)) =
      (padicValInt p (rationalPointDelta a b) : ℕ∞) := by
  have hnum : rationalPointNumerator b = 1 := by
    rw [rationalPointNumerator, ite_eq_left hb]
  have hden : rationalPointDenominator b = 0 := by
    rw [rationalPointDenominator, ite_eq_left hb]
  have hdet := rationalPoint_coordinateDeterminant_ne_zero a b hab
  rw [hnum, hden, coordinateDeterminant, mul_zero, mul_one, zero_sub] at hdet
  have hva : rationalPointDenominator a ≠ 0 := neg_ne_zero.mp hdet
  rw [rationalSectionIntersectionIdeal_at_infinity p a b hb,
    rationalPointDelta, ite_eq_left hb]
  exact integerProjectiveInfinityIntersection_length p
    (rationalPointNumerator a) (rationalPointDenominator a) hva

end ShimizuYamaguchi26BranchedCoverings

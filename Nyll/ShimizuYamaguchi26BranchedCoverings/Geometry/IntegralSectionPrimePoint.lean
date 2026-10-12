/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.IntegerLocalizationValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ZeroSection
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The integral section point above a prime

The closed point of `Spec ℤ` defined by `p` maps under evaluation at zero
in the polynomial chart to the prime `(p, X)`. The actual integral section
is the zero section followed by a coordinate swap and the inverse Bézout
coordinate change. The same coordinate swap defines the infinity chart.
Thus the section point is exactly the inverse image of the integral
infinity point under that change of coordinates.

This identifies the point used for the general local intersection
calculation in Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The point of the integer spectrum defined by the prime `p`. -/
def integerPrimePoint (p : ℕ) [Fact p.Prime] : PrimeSpectrum ℤ :=
  ⟨IntegerPrimeIdeal p, inferInstance⟩

/-- The actual integral section point over `p` is obtained by transporting
its infinity-chart point along the inverse Bézout coordinate change. -/
theorem integralSection_at_integerPrimePoint
    (u v a b : ℤ) (hab : a * u + b * v = 1) (p : ℕ) [Fact p.Prime] :
    integralSection u v a b hab (integerPrimePoint p) =
      (integralCoordinateChange u v a b hab).inv (integerProjectiveInfinityPoint p) := by
  have hpoint : PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ℤ))
      (integerPrimePoint p) = integerInfinityChartPoint p := by
    apply PrimeSpectrum.ext
    change (IntegerPrimeIdeal p).comap (Polynomial.evalRingHom (0 : ℤ)) =
      (IntegerPrimeIdeal p).comap Polynomial.constantCoeff
    have heval : Polynomial.evalRingHom (0 : ℤ) = Polynomial.constantCoeff :=
      RingHom.ext (fun f : Polynomial ℤ => f.coeff_zero_eq_eval_zero.symm)
    exact congrArg (fun ev : Polynomial ℤ →+* ℤ => (IntegerPrimeIdeal p).comap ev) heval
  change (integralCoordinateChange u v a b hab).inv
      (infinityChartEmbedding ℤ
        (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : ℤ)) (integerPrimePoint p))) =
    (integralCoordinateChange u v a b hab).inv
      (infinityChartEmbedding ℤ (integerInfinityChartPoint p))
  exact congrArg (fun q : PrimeSpectrum (Polynomial ℤ) =>
    (integralCoordinateChange u v a b hab).inv (infinityChartEmbedding ℤ q)) hpoint

end ShimizuYamaguchi26BranchedCoverings

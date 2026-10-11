/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_placeOfPoint_algebraMap

/-!
# Place ramification Index Along eq ord sub of restrict Along eq place Of Point
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
private theorem AlgebraicCurve.Place.solution_impl
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F) (a : K)
    (hwa : w.restrictAlong φ hφ = AlgebraicCurve.RationalFunctionField.placeOfPoint K a) :
    (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) =
      w.ord (φ (RatFunc.X : RatFunc K) - algebraMap K F a) := by
  classical
  have key := AlgebraicCurve.Place.ord_restrictAlong φ hφ w
    ((RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) a)
  rw [map_sub, AlgHom.commutes] at key
  rw [hwa] at key
  have hpoly : (RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) a =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a) := by
    simp [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [hpoly, ord_placeOfPoint_algebraMap a (Polynomial.X_sub_C_ne_zero a)] at key
  simp only [Polynomial.rootMultiplicity_X_sub_C_self, Nat.cast_one, mul_one] at key
  exact key.symm

theorem
  _root_.AlgebraicCurve.Place.ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint {K
  F : Type*} [Field K] [Field F] [Algebra K F] (φ : RatFunc K →ₐ[K] F)
  (hφ : φ.toRingHom.IsIntegral) (w : AlgebraicCurve.Place K F) (a : K) (hwa : w.restrictAlong φ hφ
  = AlgebraicCurve.RationalFunctionField.placeOfPoint K a) :
    (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) =
      w.ord (φ (RatFunc.X : RatFunc K) - algebraMap K F a) := by
  classical
  exact AlgebraicCurve.Place.solution_impl φ hφ w a hwa
end Place_ramificationIndexAlong_eq_ord_sub_of_restrictAlong_eq_placeOfPoint
end AlgebraicCurves.Places.Proofs
end ProofImplementation

attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

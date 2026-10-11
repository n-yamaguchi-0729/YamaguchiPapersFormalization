/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Rational.Infinity
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.Places.Rational.Classification
import AlgebraicCurves.Places.Place_mem_iff_ord_nonneg

/-!
# Rational Function Field eq place Infty of ord X neg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_eq_placeInfty_of_ord_X_neg
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve

open AlgebraicCurve

namespace S09CD

theorem eq_placeInfty_of_ord_X_neg {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K
  (RatFunc K))
    (hv : v.ord (RatFunc.X : RatFunc K) < 0) : v = RationalFunctionField.placeInfty K := by
  rcases RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | h
  · exfalso
    have hmem := RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum (K := K) w Polynomial.X
    rw [RatFunc.algebraMap_X] at hmem
    have := (Place.mem_iff_ord_nonneg _ RatFunc.X_ne_zero).mp hmem
    omega
  · exact h

end S09CD

theorem _root_.AlgebraicCurve.RationalFunctionField.eq_placeInfty_of_ord_X_neg {K : Type*} [Field
  K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : v.ord (RatFunc.X : RatFunc K) < 0) :
  v = RationalFunctionField.placeInfty K :=
  S09CD.eq_placeInfty_of_ord_X_neg v hv
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_eq_placeInfty_of_ord_X_neg
end ProofImplementation

attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

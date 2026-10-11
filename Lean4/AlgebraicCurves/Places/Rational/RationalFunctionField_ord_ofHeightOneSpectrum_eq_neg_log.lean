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

import Mathlib.FieldTheory.RatFunc.Basic
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Place_ord_eq_neg_log_of_valuationSubring_eq

/-!
# RationalFunctionField ord ofHeightOneSpectrum eq neg log

Orders at polynomial height-one places are the negative logarithms of the corresponding adic
valuations.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log {K :
  Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K}
  (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) :
  (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f = -WithZero.log (w.valuation
  (RatFunc K) f) := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  exact (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval hf
end RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation

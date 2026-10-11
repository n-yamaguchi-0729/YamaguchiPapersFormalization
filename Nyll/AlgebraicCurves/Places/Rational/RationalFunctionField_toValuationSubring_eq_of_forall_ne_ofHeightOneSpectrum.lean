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

import Mathlib.NumberTheory.RatFunc.Ostrowski
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Place_adicValuation_isRankOneDiscrete
import Nyll.AlgebraicCurves.Places.Place_adicValuation_isTrivialOn
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.Util.WithWeakNamespace

/-!
# RationalFunctionField toValuationSubring eq of forall ne ofHeightOneSpectrum

A place outside the polynomial height-one spectrum has the valuation subring of the valuation at
infinity.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs
namespace RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
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

with_weak_namespace _root_.AlgebraicCurve.RationalFunctionField
theorem toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K]
  [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w :
  IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) :
  v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  have := v.adicValuation_isRankOneDiscrete
  have := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)
end RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
end AlgebraicCurves.Places.Rational.Proofs
end ProofImplementation

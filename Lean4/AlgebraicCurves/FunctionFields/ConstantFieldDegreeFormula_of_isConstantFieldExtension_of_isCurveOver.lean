/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ConstantExtension
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Places.Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import AlgebraicCurves.Places.Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver

/-!
# Constant Field Degree Formula of is Constant Field Extension of is Curve Over
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.ConstantFieldDegreeFormula
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
open AlgebraicCurve in
theorem _root_.AlgebraicCurve.constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [PerfectField K] [Algebra.IsAlgebraic K K'] [Algebra.IsIntegral F F']
    [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range) :
    AlgebraicCurve.ConstantFieldDegreeFormula K K' F F' := by
  classical
  have : Algebra.IsSeparable K K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : HasPrincipalDivisors K' F' := IsCurveOver.hasPrincipalDivisors
  refine ⟨fun D => ?_⟩
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, Divisor.pullbackConstants_single]
    congr 1
    rw [map_sum, Divisor.degree_single]
    simp only [Divisor.degree_single]
    have he : ∀ W : Place K' F', (W.forgetConstants (K := K)).ramificationIndex F = 1 := fun W =>
      Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgen hconst W
    simp only [he, Nat.cast_one, mul_one]
    rw [← Finset.mul_sum, Place.sum_deg_fiberConstants_eq_deg_of_isCurveOver hgen hconst v]
end AlgebraicCurves.FunctionFields.Proofs.ConstantFieldDegreeFormula
end ProofImplementation

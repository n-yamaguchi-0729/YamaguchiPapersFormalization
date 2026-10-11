/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_isAlgClosed_of_transcendental
import Nyll.AlgebraicCurves.FunctionFields.Exists_separating_transcendental_of_perfectField
import Nyll.AlgebraicCurves.Places.Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Nyll.AlgebraicCurves.FunctionFields.ConstantsAreBase_of_deg_eq_one

/-!
# Constants Are Base of is Alg Closed of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.ConstantsAreBase_of_isAlgClosed_of_transcendental
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve

theorem _root_.AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ConstantsAreBase K F := by
  have hICO : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  obtain ⟨t, htr_t, hfd_t, hsep_t⟩ :=
    exists_separating_transcendental_of_perfectField (K := K) (F := F) hx inferInstance
  have : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := hfd_t
  have : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := hsep_t
  have hxIC : x ∉ (integralClosure K F).toSubring := fun h ↦ hx h.isAlgebraic
  obtain ⟨V, hICV, hxV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure K F).toSubring) hxIC
  have hKV : ∀ a : K, (RingHom.id F) (algebraMap K F a) ∈ V := fun a ↦
    hICV (Subalgebra.algebraMap_mem (integralClosure K F) a)
  obtain ⟨v₀, -⟩ :=
    Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (K := K) (F := F) (F' := F)
      t (RingHom.id F) V hKV ⟨x, hxV⟩
  exact constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
end AlgebraicCurves.FunctionFields.Proofs.ConstantsAreBase_of_isAlgClosed_of_transcendental
end ProofImplementation

attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

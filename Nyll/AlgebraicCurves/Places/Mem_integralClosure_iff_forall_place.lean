/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_mem_integralClosure_iff_forall_place.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional
import Nyll.AlgebraicCurves.Valuations.ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin

/-!
# Mem integral Closure iff forall place
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Mem_integralClosure_iff_forall_place
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
open AlgebraicCurve.Place in
attribute [-instance] instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
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
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

universe u v

open AlgebraicCurve

theorem _root_.AlgebraicCurve.mem_integralClosure_iff_forall_place
    {k : Type u} [Field k] [PerfectField k] {K : Type v} [Field K] [Algebra k K]
    [IsCurveOver k K] [Algebra.EssFiniteType k K]
    (R : Subalgebra k K) (f : K) :
    f ∈ integralClosure R K ↔
      ∀ v : Place k K, (R : Set K) ⊆ v.toValuationSubring → f ∈ v.toValuationSubring := by
  classical
  constructor
  · intro hf v hRv
    have hf' : IsIntegral R f := hf
    obtain ⟨p, hp, hpf⟩ := hf'
    have hle : R.toSubring ≤ v.toValuationSubring.toSubring := fun x hx => hRv hx
    have hint : IsIntegral v.toValuationSubring f := by
      refine ⟨p.map (Subring.inclusion hle), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpf
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.toValuationSubring) (K := K)).mp
      hint
    rw [← hy]
    exact y.2
  · intro h
    by_contra hf
    have hf' : f ∉ (integralClosure R K).toSubring := hf
    obtain ⟨V, hRV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hf'
    have hVtop : V ≠ ⊤ := fun h => hfV (h ▸ ValuationSubring.mem_top f)
    have hkV : ∀ a : k, algebraMap k K a ∈ V := fun a =>
      hRV (show algebraMap k K a ∈ (integralClosure R K).toSubring from
        (integralClosure R K).algebraMap_mem (⟨algebraMap k K a, R.algebraMap_mem a⟩ : R))
    obtain ⟨t, -, hfd, -⟩ :=
      (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := k) (F :=
      K)).mp inferInstance
    have := hfd
    have hPIR : IsPrincipalIdealRing V :=
      ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin t V hkV hVtop
    let v : Place k K :=
      { toValuationSubring := V
        algebraMap_mem' := hkV
        ne_top' := hVtop
        isPrincipalIdealRing' := hPIR }
    refine hfV (h v fun x hx => ?_)
    exact hRV (show x ∈ (integralClosure R K).toSubring from (integralClosure R K).algebraMap_mem
      (⟨x, hx⟩ : R))
end AlgebraicCurves.Places.Proofs.Mem_integralClosure_iff_forall_place
end ProofImplementation

attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single
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

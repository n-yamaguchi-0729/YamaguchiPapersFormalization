/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Models.IsAffineOpen_of_maximal_domain
import Nyll.AlgebraicCurves.Models.Exists_transcendental_mem_range_stalk_iff_ne
import Nyll.AlgebraicCurves.FunctionFields.Infinite_setOf_isClosed_singleton
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Opens_range_algebraMap_functionField_eq_iInf

/-!
# Exists isAffineOpen forall mem of finset

A finite collection of points on a proper smooth integral curve is contained in an affine open.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.Exists_isAffineOpen_forall_mem_of_finset
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler
attribute [-instance] AlgebraicCurve.IsCurveOver.instFreeKaehler
attribute [-instance] AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
attribute [-instance] AlgebraicCurve.IsCurveOver.instFiniteResidue
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Polynomial

theorem _root_.AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (F : Finset C) : ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  classical
  have hinf := AlgebraicCurve.infinite_setOf_isClosed_singleton c
  obtain ⟨Q, hQ, hQF⟩ := (hinf.sdiff F.finite_toSet).nonempty
  obtain ⟨Q', hQ', hQ'Q⟩ := (hinf.sdiff (Set.finite_singleton Q)).nonempty
  simp only [Set.mem_ofPred_eq] at hQ hQ'
  obtain ⟨f, hf, hfQ⟩ := AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne c Q hQ
  let U : C.Opens := ⟨({Q} : Set C)ᶜ, hQ.isOpen_compl⟩
  have hU_mem : ∀ x : C, x ∈ U ↔ x ≠ Q := fun x => by
    change x ∈ ({Q} : Set C)ᶜ ↔ x ≠ Q
    simp
  have : Nonempty U := ⟨⟨Q', (hU_mem Q').mpr (by simpa using hQ'Q)⟩⟩
  have hfU : f ∈ (algebraMap Γ(C, U) C.functionField).range := by
    rw [AlgebraicGeometry.Scheme.Opens.range_algebraMap_functionField_eq_iInf]
    simp only [Subring.mem_iInf]
    exact fun x hx => (hfQ x).mpr ((hU_mem x).mp hx)
  obtain ⟨s, hs⟩ := hfU
  have hgerm : C.germToFunctionField U s = f := hs
  refine ⟨U, ?_, fun x hx => (hU_mem x).mpr fun h => hQF (h ▸ hx)⟩
  refine AlgebraicCurve.isAffineOpen_of_maximal_domain c U s (fun x hx => ?_) ?_
  · rw [hgerm] at hx
    exact (hU_mem x).mpr ((hfQ x).mp hx)
  · rw [hgerm]
    exact hf
end AlgebraicCurves.Models.Proofs.Exists_isAffineOpen_forall_mem_of_finset
end ProofImplementation

attribute [-instance] AlgebraicCurve.CurveModel.isProper
attribute [-instance] AlgebraicCurve.CurveModel.isIntegral
attribute [-instance] AlgebraicCurve.CurveModel.smooth
open _root_.AlgebraicCurve.Place
  (instIsScalarTowerSubtypeMemValuationSubringToValuationSubring)
in
attribute [-instance]
  instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
attribute [-instance] AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
attribute [-instance] AlgebraicCurve.Place.instSMulAlgEquiv
open _root_.AlgebraicCurve.Place
  (instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring)
in
attribute [-instance]
  instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
open _root_.AlgebraicCurve.Place
  (instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring)
in
attribute [-instance]
  instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
attribute [-instance] AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
attribute [-instance] AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
attribute [-instance] AlgebraicCurve.Place.instMulActionAlgEquiv
attribute [-instance] AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler
attribute [-instance] AlgebraicCurve.IsCurveOver.instFreeKaehler
attribute [-instance] AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
attribute [-instance] AlgebraicCurve.IsCurveOver.instFiniteResidue
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
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
  AlgebraicCurve.Place.differentialCoeff_zero
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

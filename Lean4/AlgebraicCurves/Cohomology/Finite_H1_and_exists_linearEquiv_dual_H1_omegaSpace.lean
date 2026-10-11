/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_genus_riemannIndex_of_isCurveOver
import AlgebraicCurves.Cohomology.Exists_linearEquiv_adeleSpaceQuot_H1

/-!
# Finite H1 and exists linear Equiv dual H1 omega Space
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.FiniteH1ExistsEquivDualH1Omega
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

theorem finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace' {K : Type*} {F : Type*} [Field K]
  [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (hC : ConstantsAreBase K F) (D : Divisor K F) :
    Module.Finite K (H1 D) ∧
      ∃ e : Module.Dual K (H1 D) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) D),
        ∀ (φ : Module.Dual K (H1 D)) (a : ↥(adeleSpace K F))
          (ha : (a : Place K F → F) ∈ repartitions K F),
          (e φ : Module.Dual K ↥(adeleSpace K F)) a
            = φ (Submodule.Quotient.mk ⟨(a : Place K F → F), ha⟩) := by
  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hC
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_adeleSpaceQuot_H1 (K := K) (F := F) D
  have : Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) := (hγ D).1
  refine ⟨Module.Finite.equiv e₁, ⟨e₁.dualMap.trans (omegaSpaceEquivIndexDual D).symm, ?_⟩⟩
  intro φ a ha
  rw [← he₁ a ha]
  rfl

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Cohomology.Proofs.FiniteH1ExistsEquivDualH1Omega.AlgebraicCurve in
theorem _root_.AlgebraicCurve.finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace {K : Type*} {F :
  Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (hC : ConstantsAreBase K F) (D : Divisor K F) :
    Module.Finite K (H1 D) ∧
      ∃ e : Module.Dual K (H1 D) ≃ₗ[K] ↥(omegaSpace (K := K) (F := F) D),
        ∀ (φ : Module.Dual K (H1 D)) (a : ↥(adeleSpace K F))
          (ha : (a : Place K F → F) ∈ repartitions K F),
          (e φ : Module.Dual K ↥(adeleSpace K F)) a
            = φ (Submodule.Quotient.mk ⟨(a : Place K F → F), ha⟩) :=
  AlgebraicCurve.finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace' hC D
end AlgebraicCurves.Cohomology.Proofs.FiniteH1ExistsEquivDualH1Omega
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

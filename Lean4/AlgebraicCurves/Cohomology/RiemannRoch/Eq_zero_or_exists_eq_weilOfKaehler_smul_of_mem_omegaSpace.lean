/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Cohomology.SerrePairing
import AlgebraicCurves.Cohomology.RiemannRoch
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_weilSmul_eq_of_riemannIndexFormula

/-!
# Eq zero or exists eq weil Of Kaehler smul of mem omega Space
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.EqZeroOrExistsWeilOfKaehlerSmul
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

namespace ModularCurve
namespace OmegaSide
namespace A

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kaehlerResidueTerm_smulF_left [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F]
    (f : F) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (f • ω) α v = kaehlerResidueTerm ω (mulAdele K f α) v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul, mulAdele_apply]
  ring_nf

theorem weilOfKaehler_smulF [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F] [HasCanonicalDivisor (K := K)
      (F := F)]
    {f : F} {ω : Ω[F⁄K]} (hω : ω ≠ 0) (hf : f ≠ 0) :
    weilOfKaehler K F (ω := f • ω) (smul_ne_zero hf hω) = weilSmul K F f (weilOfKaehler K F hω)
      := by
  apply LinearMap.ext
  intro α
  rw [weilSmul_apply, weilOfKaehler_apply, weilOfKaehler_apply]
  refine finsum_congr fun v => ?_
  rw [kaehlerResidueTerm_smulF_left, adeleSpaceMul_coe]

theorem eq_zero_or_exists_eq_weilOfKaehler_smul'
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]
    (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (D : Divisor K F)
    (μ : Module.Dual K (adeleSpace K F)) (hμ : μ ∈ omegaSpace (K := K) (F := F) D) :
    μ = 0 ∨ ∃ (f : F) (hf : f ≠ 0), μ = weilOfKaehler K F (ω := f • ω₀) (smul_ne_zero hf hω₀) := by
  classical
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨hl0, hlmem, hlmax⟩ := hagree hω₀
  set W₀ := canonicalDivisorOf hω₀
  have h1 : omegaSpace (K := K) (F := F) W₀ ≤ omegaSpace (W₀ ⊓ D) := omegaSpace_antitone inf_le_left
  have h2 : omegaSpace (K := K) (F := F) D ≤ omegaSpace (W₀ ⊓ D) := omegaSpace_antitone inf_le_right
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_riemannIndexFormula hRI (h1 hlmem) (h2 hμ) hl0
  by_cases hf0 : f = 0
  · left
    rw [hf, hf0]
    apply LinearMap.ext; intro α
    rw [weilSmul_apply, LinearMap.zero_apply]
    have : adeleSpaceMul K F (0 : F) α = 0 := by
      apply Subtype.ext; rw [adeleSpaceMul_coe]; funext v; simp [mulAdele_apply]
    rw [this, map_zero]
  · right
    exact ⟨f, hf0, by rw [weilOfKaehler_smulF hω₀ hf0, hf]⟩

end ModularCurve.OmegaSide.A

open ModularCurve.OmegaSide.A in
theorem _root_.AlgebraicCurve.eq_zero_or_exists_eq_weilOfKaehler_smul_of_mem_omegaSpace
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasCanonicalLocalResidueKStar K F]
    (hRI : RiemannIndexFormula K F) (hagree : WeilKaehlerAgree K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (D : Divisor K F)
    (μ : Module.Dual K (adeleSpace K F)) (hμ : μ ∈ omegaSpace (K := K) (F := F) D) :
    μ = 0 ∨ ∃ (f : F) (hf : f ≠ 0), μ = weilOfKaehler K F (ω := f • ω₀) (smul_ne_zero hf hω₀) :=
  eq_zero_or_exists_eq_weilOfKaehler_smul' hRI hagree hω₀ D μ hμ
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.EqZeroOrExistsWeilOfKaehlerSmul
end ProofImplementation

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.serrePairing_apply_mk
  AlgebraicCurve.residueSumOffChartLinear_apply AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

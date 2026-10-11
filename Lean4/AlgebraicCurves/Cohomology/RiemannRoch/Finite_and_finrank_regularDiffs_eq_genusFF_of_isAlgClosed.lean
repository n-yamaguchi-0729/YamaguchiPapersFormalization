/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Cohomology.RiemannRoch
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.Cohomology.RiemannRoch.Finite_and_finrank_regularDifferentials_eq_genus
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed_of_transcendental
import AlgebraicCurves.Cohomology.RiemannRoch.Eq_genusFF_of_forall_ell_sub_ell_eq
import AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq_of_ord_eq_one
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_eq_one
import AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField

/-!
# Finite and finrank regular Diffs eq genus FF of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteFinrankRegularDiffsGenusFF
open _root_.IsDedekindDomain.HeightOneSpectrum in
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
attribute [-instance] AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
attribute [-simp] AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

universe u v

open AlgebraicCurve KaehlerDifferential IntermediateField

namespace GenusRegDiffs

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem mem_iff_ord_nonneg (w : Place K F) {x : F} (hx : x ≠ 0) :
    x ∈ w.toValuationSubring ↔ 0 ≤ w.ord x := by
  rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
    WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx), WithZero.exp_zero]

theorem mem_of_ord_nonneg (w : Place K F) {x : F} (h : 0 ≤ w.ord x) : x ∈ w.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  · exact (mem_iff_ord_nonneg w hx).mpr h

theorem ord_nonneg_of_mem (w : Place K F) {x : F} (h : x ∈ w.toValuationSubring) : 0 ≤ w.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Place.ord_zero]
  · exact (mem_iff_ord_nonneg w hx).mp h

theorem key [PerfectField K] (x : F) [FiniteDimensional K⟮x⟯ F] (ω : Ω[F⁄K]) (v : Place K F) :
    0 ≤ v.ordDiff ω ↔ ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord := by
  have : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨π, hπ, hdc⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨π, hπ⟩
  have hc : Place.diffCoeff v.uniformizer_alt (D K F π) • D K F v.uniformizer_alt = D K F π :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht _
  have hc' : Place.diffCoeff π (D K F v.uniformizer_alt) • D K F π = D K F v.uniformizer_alt :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v hπ _
  have hc0 : 0 ≤ v.ord (Place.diffCoeff v.uniformizer_alt (D K F π)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht (by rw [hπ]; exact zero_le_one)
  have hc'0 : 0 ≤ v.ord (Place.diffCoeff π (D K F v.uniformizer_alt)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField x v hπ (by rw [ht]; exact zero_le_one)
  have hcc' : Place.diffCoeff π (D K F v.uniformizer_alt) * Place.diffCoeff v.uniformizer_alt (D K
    F π) = 1 := by
    have h1 : (Place.diffCoeff π (D K F v.uniformizer_alt) * Place.diffCoeff v.uniformizer_alt (D
      K F π)) •
        D K F v.uniformizer_alt = (1 : F) • D K F v.uniformizer_alt := by
      rw [mul_smul, hc, hc', one_smul]
    have h := congrArg (Place.diffCoeff v.uniformizer_alt) h1
    rwa [Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht,
      Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht] at h
  have hcne : Place.diffCoeff v.uniformizer_alt (D K F π) ≠ 0 := fun h => by
    rw [h, mul_zero] at hcc'; exact zero_ne_one hcc'
  have hc'ne : Place.diffCoeff π (D K F v.uniformizer_alt) ≠ 0 := fun h => by
    rw [h, zero_mul] at hcc'; exact zero_ne_one hcc'
  have hordc : v.ord (Place.diffCoeff v.uniformizer_alt (D K F π)) = 0 := by
    have h := v.ord_mul hc'ne hcne
    rw [hcc', Place.ord_one] at h
    linarith
  rw [Place.ordDiff_def]
  constructor
  · intro h
    refine ⟨Place.diffCoeff v.uniformizer_alt ω * Place.diffCoeff π (D K F v.uniformizer_alt), ?_,
      ?_⟩
    · refine mem_of_ord_nonneg v ?_
      rcases eq_or_ne (Place.diffCoeff v.uniformizer_alt ω) 0 with h0 | h0
      · rw [h0, zero_mul, Place.ord_zero]
      · rw [v.ord_mul h0 hc'ne]; exact add_nonneg h hc'0
    · rw [hdc, mul_smul, hc', Place.diffCoeff_smul_D_of_ord_eq_one x v ht ω]
  · rintro ⟨f, hf, rfl⟩
    rw [hdc, ← hc, smul_smul, Place.diffCoeff_smul_D_eq_of_ord_eq_one x v ht]
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [zero_mul, Place.ord_zero]
    · rw [v.ord_mul hf0 hcne, hordc, add_zero]; exact ord_nonneg_of_mem v hf

theorem regularDiffs_eq [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    regularDiffs K F = regularDifferentials K F := by
  obtain ⟨x, -, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have := hfin
  apply le_antisymm
  · rw [regularDiffs_eq_span]
    refine Submodule.span_le.mpr fun ω hω => ?_
    rw [SetLike.mem_coe, mem_regularDifferentials_iff]
    exact fun v => (key x ω v).mp (hω v)
  · intro ω hω
    rw [mem_regularDifferentials_iff] at hω
    exact mem_regularDiffs_of_isRegularDiff fun v => (key x ω v).mpr (hω v)

end GenusRegDiffs

theorem _root_.AlgebraicCurve.finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F] :
    Module.Finite K ↥(AlgebraicCurve.regularDiffs K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDiffs K F) = AlgebraicCurve.genusFF K F := by
  classical
  have : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  have : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨t, ht, htfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have := htfd
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hRR : FunctionFieldRiemannRoch K F :=
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental ht htfd
  obtain ⟨h1, h2⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
  rw [GenusRegDiffs.regularDiffs_eq]
  refine ⟨h1, h2.trans ?_⟩
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  exact eq_genusFF_of_forall_ell_sub_ell_eq hC (Kc := canonicalDivisorOf hω₀) (g := genus K F)
    (fun D => hRR hω₀ D)
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FiniteFinrankRegularDiffsGenusFF
end ProofImplementation

open _root_.IsDedekindDomain.HeightOneSpectrum in
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
attribute [-instance] AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.coe_torsion_smul
  AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

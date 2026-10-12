/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.AffineLimit
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.SchemeTheory.Descent.FGSubalgebra
import Nyll.AlgebraicCurves.Geometry.Schemes.FGSubalgebra_nonempty_isLimit_specCone
import Nyll.JacobianVarieties.Picard.IsAlgEquivZero_iff_eulerChar_sectionsOf_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Geometry.Picard.Exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import Nyll.JacobianVarieties.Picard.Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq
import Nyll.JacobianVarieties.Picard.IsLFPSurj_relPicardPresheaf
import Nyll.JacobianVarieties.Picard.IsOpen_setOf_isAlgEquivZero_fibre

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Opposites

/-!
# Finite presentation surjectivity for the algebraically trivial Picard presheaf

Descend a rigidified line bundle to a finitely generated subalgebra, then enlarge that
subalgebra so its fibres are algebraically trivial. Openness of the triviality locus
and the affine limit comparison ensure that the descended class has the required property.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsLFPSurj_relSubPicPresheaf_algEquivZeroCut
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
attribute [-instance]
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicCurve.Place.mk.injEq
attribute [-simp]
  AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
attribute [-simp]
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
attribute [-simp]
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
attribute [-simp]
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
attribute [-simp]
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.AffineLimit

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace LfpPicSurj
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R]

theorem twoAffineOpenCover_ext {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) : 𝒱 = 𝒲 := by
  obtain ⟨U0, U1, p1, p2, p3, p4⟩ := 𝒱
  obtain ⟨U0', U1', q1, q2, q3, q4⟩ := 𝒲
  change U0 = U0' at h0
  change U1 = U1' at h1
  subst h0
  subst h1
  rfl

theorem finrank_sectionsOf_eq_of_iso {S : Type u} [CommRing S] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of S))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank S (𝒱.sectionsOf x M).H0 = Module.finrank S (𝒱.sectionsOf x M').H0 ∧
      Module.finrank S (𝒱.sectionsOf x M).H1 = Module.finrank S (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱', hU0, hU1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
    (Category.id_comp x) 𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  have h𝒱 : 𝒱' = 𝒱 := twoAffineOpenCover_ext (hU0.trans (Scheme.Hom.id_preimage _))
    (hU1.trans (Scheme.Hom.id_preimage _))
  subst h𝒱
  exact ⟨e0.finrank_eq, e1.finrank_eq⟩

lemma locallyOfFiniteType_Spec_algebraMap (A₀ : Type u) [CommRing A₀] [Algebra R A₀]
    [Algebra.FiniteType R A₀] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
  exact RingHom.finiteType_algebraMap.mpr ‹_›

lemma specOverOfSubalgebra_comp_specOverOfLE {A : Type u} [CommRing A] [Algebra R A]
    (A₀ A₁ : Subalgebra R A)
    (h : A₀ ≤ A₁) : specOverOfSubalgebra R A₁ ≫ specOverOfLE R A₀ A₁ h
      = specOverOfSubalgebra R A₀ := by
  ext : 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

lemma exists_geometricPoint (A : Type u) [CommRing A] (P : Spec (CommRingCat.of A)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      Set.range ⇑s ⊆ {P} := by
  have : P.asIdeal.IsPrime := (show PrimeSpectrum A from P).isPrime
  refine ⟨AlgebraicClosure P.asIdeal.ResidueField, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom ((algebraMap P.asIdeal.ResidueField
        (AlgebraicClosure P.asIdeal.ResidueField)).comp
      (algebraMap A P.asIdeal.ResidueField))), ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  rw [Set.mem_singleton_iff]
  apply PrimeSpectrum.ext
  change Ideal.comap _ (IsLocalRing.maximalIdeal _) = P.asIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, CommRingCat.hom_ofHom,
    ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap P.asIdeal.ResidueField _).injective,
    ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

theorem exists_algebra_eq_specMap_comp_specMap {A : Type u} [CommRing A]
    (𝔭 : PrimeSpectrum A) {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
    (hs : s (IsLocalRing.closedPoint k) = 𝔭) :
    ∃ (_ : Algebra 𝔭.asIdeal.ResidueField k),
      s = Scheme.TwoAffineOpenCover.specMap 𝔭.asIdeal.ResidueField k ≫
        Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField := by
  obtain ⟨φ, rfl⟩ : ∃ φ : A →+* k, Spec.map (CommRingCat.ofHom φ) = s :=
    ⟨(Spec.preimage s).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hker : 𝔭.asIdeal = RingHom.ker φ := by
    rw [← hs]
    change Ideal.comap φ (IsLocalRing.maximalIdeal k) = RingHom.ker φ
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hunit : 𝔭.asIdeal.primeCompl ≤ Submonoid.comap φ (IsUnit.submonoid k) := fun a ha => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    exact fun h0 => ha (show a ∈ 𝔭.asIdeal by rw [hker]; exact RingHom.mem_ker.mpr h0)
  let ψ : 𝔭.asIdeal.ResidueField →+* k := Ideal.ResidueField.lift 𝔭.asIdeal φ hker.le hunit
  let : Algebra 𝔭.asIdeal.ResidueField k := ψ.toAlgebra
  have hcomp : (algebraMap 𝔭.asIdeal.ResidueField k).comp (algebraMap A 𝔭.asIdeal.ResidueField)
      = φ := by
    ext a
    exact Ideal.ResidueField.lift_algebraMap 𝔭.asIdeal φ hker.le hunit a
  refine ⟨ψ.toAlgebra, ?_⟩
  rw [Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hcomp]

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isAlgEquivZero_fibre_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (h : IsAlgEquivZero (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) M.L)) :
    IsAlgEquivZero (fibreAt c t' s') (fibreModule c t' s' (M.pullbackAlong ψ).L) := by
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t := by
    simp only [baseChangeSnd, pullback.lift_snd]
  let e : Limits.pullback (pullback.snd c t') s' ⟶ Limits.pullback (pullback.snd c t) (s' ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ (by rw [Category.id_comp])
  have he : e ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

theorem isAlgEquivZero_fibre_of_pullbackAlong {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (h : IsAlgEquivZero (fibreAt c t' s') (fibreModule c t' s' (M.pullbackAlong ψ).L)) :
    IsAlgEquivZero (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) M.L) := by
  have hbc : IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c t)
    rw [show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
      (pullback.lift_fst _ _ _).trans (Category.comp_id _), ψ.2]
    exact IsPullback.of_hasPullback c t'
  have hP : IsPullback (pullback.fst
      (pullback.snd c t') s' ≫ baseChangeSnd c ψ) (pullback.snd (pullback.snd c t') s')
      (pullback.snd c t) (s' ≫ ψ.1) :=
    (IsPullback.of_hasPullback (pullback.snd c t') s').paste_horiz hbc
  let e := hP.isoPullback.inv
  have he : e ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := hP.isoPullback_inv_snd
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact hP.isoPullback_inv_fst)).app M.L

theorem isAlgEquivZero_fibre_of_isAlgEquivZero_fibre
    [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (L : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R A₀))))
    (P : Spec (CommRingCat.of A₀))
    {k₁ : Type u} [Field k₁] [IsAlgClosed k₁]
    (s₁ : Spec (CommRingCat.of k₁) ⟶ Spec (CommRingCat.of A₀))
    (hs₁ : Set.range ⇑s₁ ⊆ {P})
    (h₁ : IsAlgEquivZero (fibreAt c _ s₁)
        (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s₁ L.L))
    {k₂ : Type u} [Field k₂] [IsAlgClosed k₂]
    (s₂ : Spec (CommRingCat.of k₂) ⟶ Spec (CommRingCat.of A₀))
    (hs₂ : Set.range ⇑s₂ ⊆ {P}) :
    IsAlgEquivZero (fibreAt c _ s₂)
      (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s₂ L.L) := by
  have : P.asIdeal.IsPrime := (show PrimeSpectrum A₀ from P).isPrime
  obtain ⟨_, rfl⟩ := exists_algebra_eq_specMap_comp_specMap (A := A₀) P s₁ (hs₁ ⟨_, rfl⟩)
  obtain ⟨_, rfl⟩ := exists_algebra_eq_specMap_comp_specMap (A := A₀) P s₂ (hs₂ ⟨_, rfl⟩)
  obtain ⟨𝔉, -⟩ := h𝔉 0
  let : Algebra R P.asIdeal.ResidueField :=
    ((algebraMap A₀ P.asIdeal.ResidueField).comp (algebraMap R A₀)).toAlgebra
  have hRκ : Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField ≫ 𝟙 _ =
      Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) := by
    rw [Category.comp_id, Scheme.TwoAffineOpenCover.specMap, Scheme.TwoAffineOpenCover.specMap,
      ← Spec.map_comp]
    rfl
  let g' : pullback c (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField) ⟶
      pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) :=
    pullback.map _ _ _ _ (𝟙 C)
      (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) hRκ
  have hcart : IsPullback g'
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField))
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))))
      (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback c _)
    rw [show g' ≫ pullback.fst c _ = pullback.fst c _
        from (pullback.lift_fst _ _ _).trans (Category.comp_id _),
      ← Category.comp_id (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField), hRκ]
    exact IsPullback.of_hasPullback c _
  obtain ⟨𝒲₀, -, -⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c
    (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) L.L
      (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R P.asIdeal.ResidueField)) g' hcart
    ((Scheme.Modules.pullback g').obj L.L) (Iso.refl _)
    (𝔉.twoAffineOpenCover.pullback c P.asIdeal.ResidueField)
  obtain ⟨𝒲₁, h𝒲₁⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq c
    (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) 𝒲₀ k₁
  obtain ⟨𝒲₂, h𝒲₂⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_finrank_H1_eq c
    (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) 𝒲₀ k₂
  obtain ⟨hL0₁, hL1₁⟩ := h𝒲₁ L.L L.isInvertible
  obtain ⟨hO0₁, hO1₁⟩ := h𝒲₁
    (SheafOfModules.unit
      (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf)
    (Scheme.Modules.isInvertible_unit _)
  obtain ⟨hL0₂, hL1₂⟩ := h𝒲₂ L.L L.isInvertible
  obtain ⟨hO0₂, hO1₂⟩ := h𝒲₂
    (SheafOfModules.unit
      (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf)
    (Scheme.Modules.isInvertible_unit _)
  have hsm : SmoothOfRelativeDimension 1
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) :=
    _root_.AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd 1 c
      (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
  have inst : ∀ {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A₀)),
      IsProper (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s) ∧
      SmoothOfRelativeDimension 1 (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s) ∧
      IsIntegral (pullback (pullback.snd c
          (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) s) := by
    intro k _ s
    have : GeometricallyIntegral (fibreAt c
        (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s) := by
      unfold fibreAt; infer_instance
    refine ⟨by unfold fibreAt; infer_instance,
      by
        unfold fibreAt
        exact _root_.AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd 1
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))) s, ?_⟩
    exact GeometricallyIntegral.isIntegral_of_subsingleton
      (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀))) s)
  obtain ⟨hp₁, hs₁', hi₁⟩ := inst (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫
    Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
  obtain ⟨hp₂, hs₂', hi₂⟩ := inst (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫
    Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
  have hu₁ := finrank_sectionsOf_eq_of_iso
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)) 𝒲₁
    (M := fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
      (SheafOfModules.unit
        (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf))
    (Scheme.Modules.pullbackUnitIso _)
  have hu₂ := finrank_sectionsOf_eq_of_iso
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)) 𝒲₂
    (M := fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField)
      (SheafOfModules.unit
        (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))).ringCatSheaf))
    (Scheme.Modules.pullbackUnitIso _)
  obtain ⟨hu0₁, hu1₁⟩ := hu₁
  obtain ⟨hu0₂, hu1₂⟩ := hu₂
  have hχ₁ := (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k₁
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField))
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₁ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) L.L)
    (L.isInvertible.pullback _) 𝒲₁).mp h₁
  refine (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k₂
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField))
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
      (Scheme.TwoAffineOpenCover.specMap P.asIdeal.ResidueField k₂ ≫
        Scheme.TwoAffineOpenCover.specMap A₀ P.asIdeal.ResidueField) L.L)
    (L.isInvertible.pullback _) 𝒲₂).mpr ?_
  omega

theorem exists_fg_preimage_eq_top {A : Type u} [CommRing A] [Algebra R A]
    (A₀ : Subalgebra R A) (hA₀ : A₀.FG)
    (W : (Spec (CommRingCat.of ↥A₀)).Opens)
    (hW : Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ⁻¹ᵁ W = ⊤) :
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (hle : A₀ ≤ A₁),
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom) ⁻¹ᵁ W = ⊤ := by
  have : Nonempty (FGSubalgebra R A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirected (FGSubalgebra R A) (· ≤ ·) :=
    ⟨fun D E => ⟨⟨D.1 ⊔ E.1, D.2.sup E.2⟩,
      (le_sup_left : D.1 ≤ D.1 ⊔ E.1), (le_sup_right : E.1 ≤ D.1 ⊔ E.1)⟩⟩
  have : IsFiltered (FGSubalgebra R A) := inferInstance
  have : IsCofiltered (FGSubalgebra R A)ᵒᵖ := inferInstance
  have (i : (FGSubalgebra R A)ᵒᵖ) : IsAffine ((FGSubalgebra.specDiagram R A).obj i) :=
    inferInstanceAs (IsAffine (Spec _))
  have (i : (FGSubalgebra R A)ᵒᵖ) : CompactSpace ((FGSubalgebra.specDiagram R A).obj i) :=
    inferInstanceAs (CompactSpace (Spec _))
  have {i j : (FGSubalgebra R A)ᵒᵖ} (f : i ⟶ j) :
      IsAffineHom ((FGSubalgebra.specDiagram R A).map f) := isAffineHom_of_isAffine _
  obtain ⟨hc⟩ := FGSubalgebra.nonempty_isLimit_specCone R A
  obtain ⟨j, f, hf⟩ := _root_.AlgebraicGeometry.exists_map_eq_top
    (FGSubalgebra.specDiagram R A) (FGSubalgebra.specCone R A) hc
    (i := op ⟨A₀, hA₀⟩) W hW
  exact ⟨j.unop.1, j.unop.2, f.unop.le, hf⟩

end AlgebraicGeometry.RelPicard.LfpPicSurj

open AlgebraicGeometry.RelPicard.LfpPicSurj in
theorem _root_.AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) :
    IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by
  classical
  intro A _ _ x
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨A₀, hA₀, y₀, hy₀⟩ := isLFPSurj_relPicardPresheaf R 𝔉.twoAffineOpenCover c ε A x.1
  obtain ⟨L₀, rfl⟩ := Quotient.exists_rep y₀
  have : Algebra.FiniteType R ↥A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀))) :=
    locallyOfFiniteType_Spec_algebraMap ↥A₀
  have : LocallyOfFiniteType (unop (op (specOver R ↥A₀))).hom :=
    locallyOfFiniteType_Spec_algebraMap ↥A₀
  have hx2 : FibrewiseAlgEquivZero
      (L₀.pullbackAlong ⟨(specOverOfSubalgebra R A₀).left, Over.w _⟩) := by
    have h2 := x.2
    rw [← hy₀] at h2
    exact h2
  let W : (Spec (CommRingCat.of ↥A₀)).Opens :=
    ⟨{P | ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥A₀)),
        Set.range ⇑s ⊆ {P} → IsAlgEquivZero (fibreAt c _ s)
          (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀))) s L₀.L)},
      isOpen_setOf_isAlgEquivZero_fibre R c ε h𝔉 _ L₀⟩
  have himg : Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ⁻¹ᵁ W = ⊤ := by
    refine top_le_iff.mp fun Q _ => ?_
    obtain ⟨k, _, _, s, hs⟩ := exists_geometricPoint A Q
    intro k' _ _ s' hs'
    refine isAlgEquivZero_fibre_of_isAlgEquivZero_fibre c ε h𝔉 ↥A₀ L₀ _
      (s ≫ Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) ?_ ?_ s' hs'
    · rintro _ ⟨p, rfl⟩
      exact congrArg (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (hs ⟨p, rfl⟩)
    · exact isAlgEquivZero_fibre_of_pullbackAlong c ε ⟨(specOverOfSubalgebra R A₀).left, Over.w _⟩
        L₀ s (hx2 k s)
  obtain ⟨A₁, hA₁, hle, hW⟩ := exists_fg_preimage_eq_top A₀ hA₀ W himg
  refine ⟨A₁, hA₁, ⟨(relPicardPresheaf c ε).map (specOverOfLE R A₀ A₁ hle).op (Quotient.mk _ L₀),
    ?_⟩, ?_⟩
  · change FibrewiseAlgEquivZero (L₀.pullbackAlong ⟨(specOverOfLE R A₀ A₁ hle).left, Over.w _⟩)
    intro k _ _ s₁
    have hP : (specOverOfLE R A₀ A₁ hle).left (s₁ (IsLocalRing.closedPoint k)) ∈ W := by
      have : s₁ (IsLocalRing.closedPoint k) ∈ (⊤ : (Spec (CommRingCat.of ↥A₁)).Opens) := trivial
      rwa [← hW] at this
    refine isAlgEquivZero_fibre_pullbackAlong c ε _ L₀ s₁
      (hP k (s₁ ≫ (specOverOfLE R A₀ A₁ hle).left) ?_)
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rfl
  · apply Subtype.ext
    change (relPicardPresheaf c ε).map (specOverOfSubalgebra R A₁).op
        ((relPicardPresheaf c ε).map (specOverOfLE R A₀ A₁ hle).op (Quotient.mk _ L₀)) = x.1
    let F := relPicardPresheaf c ε
    let q₀ : F.obj (op (specOver R ↥A₀)) := Quotient.mk _ L₀
    have hsource : (specOverOfLE R A₀ A₁ hle).op ≫ (specOverOfSubalgebra R A₁).op =
        (specOverOfSubalgebra R A₀).op :=
      (op_comp (f := specOverOfSubalgebra R A₁) (g := specOverOfLE R A₀ A₁ hle)).symm.trans
        (congrArg (fun h : specOver R A ⟶ specOver R ↥A₀ => h.op)
          (specOverOfSubalgebra_comp_specOverOfLE A₀ A₁ hle))
    have hmaps : F.map (specOverOfLE R A₀ A₁ hle).op ≫ F.map (specOverOfSubalgebra R A₁).op =
        F.map (specOverOfSubalgebra R A₀).op :=
      (F.map_comp (specOverOfLE R A₀ A₁ hle).op (specOverOfSubalgebra R A₁).op).symm.trans
        (congrArg (fun h : op (specOver R ↥A₀) ⟶ op (specOver R A) => F.map h) hsource)
    have hvalue := congrArg
      (fun h : F.obj (op (specOver R ↥A₀)) ⟶ F.obj (op (specOver R A)) => h q₀) hmaps
    exact hvalue.trans hy₀
end JacobianVarieties.Picard.Proofs.IsLFPSurj_relSubPicPresheaf_algEquivZeroCut
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
attribute [-instance]
  PresheafOfModules.ExteriorPower.instModulePresheafAb
  AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
  AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instNonempty
  AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
  AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsFiltered
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance]
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField
attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
attribute [-instance]
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
attribute [-simp]
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec
  AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq
attribute [-simp]
  AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
attribute [-simp]
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
attribute [-simp]
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

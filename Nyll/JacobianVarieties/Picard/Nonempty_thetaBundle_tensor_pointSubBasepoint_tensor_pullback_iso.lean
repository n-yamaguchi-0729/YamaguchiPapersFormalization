/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.JacobianVarieties.Picard.Nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback
import Nyll.AlgebraicCurves.Geometry.Picard.Subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
import Nyll.AlgebraicCurves.Geometry.Picard.Nonempty_pullback_sectionTwist_iso
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Nyll.JacobianVarieties.Picard.IsLocallyFreeOfRank_pushforward_of_forall_fibre
import Nyll.JacobianVarieties.Picard.Forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
import Nyll.JacobianVarieties.Picard.Nonempty_pullback_sectionIdeal_pow_module_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
Compare theta bundles after twisting by the difference of one point and the basepoint.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ThetaPointTwist
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
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
  AlgebraicGeometry.ChowDatum.hp_proper
attribute [-instance]
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue
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
attribute [-instance]
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
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
attribute [-instance] ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
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
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply exteriorPower.mulₗ_apply_coe
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.OModulePresheaf.prod_obj
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
  DoubleComplex.SubQuot.mk.injEq
attribute [-simp]
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
attribute [-simp]
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
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
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
attribute [-simp]
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
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

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicCurve
open _root_.GoodReductionJacobian

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace ThetaStep
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}

/-- Rigidify an invertible sheaf over the base field using the triviality of its fibre. -/
noncomputable def ofField (L : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))) where
  L := L
  isInvertible := hL
  rigidified := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hL.pullback _)

/-- Exchange the last two factors in a left-associated triple tensor product. -/
noncomputable def swapR {X : Scheme.{u}} (A B D : X.Modules) : (A ⊗ B) ⊗ D ≅ (A ⊗ D) ⊗ B :=
  α_ _ _ _ ≪≫ whiskerLeftIso A (β_ B D) ≪≫ (α_ _ _ _).symm

theorem isInvertible_sectionIdeal [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) {T : Scheme.{u}} (t : T ⟶ Spec
      (CommRingCat.of k)) :
    (sectionIdeal c Q t).IsInvertible := by
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    SmoothOfRelativeDimension.pullback_snd 1 c t
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t Q) (pullback.lift_snd _ _ _)

theorem rigSection_eq_graphOver (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    rigSection c (𝟙 (Spec (CommRingCat.of k))) Q = graphOver c Q.1 Q.2 := by
  apply pullback.hom_ext
  · simp only [rigSection, pullback.lift_fst, graphOver_fst, Category.id_comp]
  · simp only [rigSection, pullback.lift_snd, graphOver_snd]

theorem sectionIdeal_one_eq [IsSeparated c] (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    (sectionIdeal c Q (𝟙 (Spec (CommRingCat.of k)))) ^ 1 = (RelEffCartierDiv.ofPoint c Q.1 Q.2).I
      := by
  rw [pow_one, RelEffCartierDiv.ofPoint_I, sectionIdeal, rigSection_eq_graphOver]

end AlgebraicGeometry.RelPicard.ThetaStep
end JacobianVarieties.Picard.Proofs.ThetaPointTwist

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.ThetaPointTwist
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicCurve
open _root_.GoodReductionJacobian


open _root_.JacobianVarieties.Picard.Proofs in
open ThetaPointTwist.AlgebraicGeometry.RelPicard.ThetaStep in
theorem nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (s : Spec (CommRingCat.of k') ⟶ Spec
      (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra k' L] (M : CurveModel k' L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k' L) (g' : ℕ),
      (∀ D : Divisor k' L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k)))) (hN : FibrewiseAlgEquivZero N)
    (eN : N.L ≅ pointSubBasepointModule (a := c) P ε)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        (Scheme.Modules.pullback (rigSection c t P)).obj M.L ≅
      thetaBundle c ε t M r (r + 1 - g)) := by
  let S := Spec (CommRingCat.of k)
  let tT : SchemeHomOver t (𝟙 S) := ⟨t, Category.comp_id t⟩
  let π := pullback.snd c t
  let F : (pullback c t).Modules := M.L
  let Iε : (pullback c t).IdealSheafData := sectionIdeal c ε t
  let IP : (pullback c t).IdealSheafData := sectionIdeal c P t
  let Orε : (pullback c t).Modules := sectionTwist c ε t r
  let OP : (pullback c t).Modules := sectionTwist c P t 1
  let G : (pullback c t).Modules := (F ⊗ Orε) ⊗ OP
  let NT := N.pullbackAlong tT
  have hIε : Iε.IsInvertible := isInvertible_sectionIdeal ε t
  have hIP : IP.IsInvertible := isInvertible_sectionIdeal P t
  have hIεr : (Iε ^ r).IsInvertible := hIε.pow r
  have hF : Scheme.Modules.IsInvertible F := M.isInvertible
  have hOrε : Scheme.Modules.IsInvertible Orε := hIεr.isInvertible_invModule
  have hOP : Scheme.Modules.IsInvertible OP := (hIP.pow 1).isInvertible_invModule
  have hG : Scheme.Modules.IsInvertible G := (hF.tensor hOrε).tensor hOP
  have pairP : OP ⊗ IP.module ≅ 𝟙_ _ :=
    whiskerRightIso (eqToIso (by rw [pow_one] : (IP ^ 1).invModule = IP.invModule)) _ ≪≫
      (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hIP).some
  have pairε : Iε.invModule ⊗ Iε.module ≅ 𝟙_ _ :=
    (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hIε).some
  have ea : G ⊗ IP.module ≅ F ⊗ Orε := α_ _ _ _ ≪≫ whiskerLeftIso _ pairP ≪≫ ρ_ _
  obtain ⟨bcP⟩ := RelPicard.nonempty_pullback_sectionTwist_iso k c P tT 1
  obtain ⟨bcε⟩ := RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso k c ε tT 1
  have eNT : NT.L ≅ OP ⊗ Iε.module :=
    (Scheme.Modules.pullback _).mapIso eN ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((Scheme.Modules.pullback _).mapIso (eqToIso
          (congrArg Scheme.IdealSheafData.invModule (sectionIdeal_one_eq (c := c) P).symm)) ≪≫ bcP)
            ⊗ᵢ
        ((Scheme.Modules.pullback _).mapIso (eqToIso
          (congrArg Scheme.IdealSheafData.module (sectionIdeal_one_eq (c := c) ε).symm)) ≪≫ bcε ≪≫
          eqToIso (by rw [pow_one])))
  have eb : G ⊗ Iε.module ≅ (M.tensor NT).L ⊗ Orε :=
    α_ _ _ _ ≪≫ swapR _ _ _ ≪≫ whiskerRightIso (whiskerLeftIso F eNT.symm) _
  have eSucc : sectionTwist c ε t (r + 1) ≅ Orε ⊗ Iε.invModule :=
    eqToIso (by rw [pow_succ] : (Iε ^ (r + 1)).invModule = (Iε ^ r * Iε).invModule) ≪≫
      (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hIεr hIε).some
  have ec : G ≅ (M.tensor NT).L ⊗ sectionTwist c ε t (r + 1) :=
    (ρ_ G).symm ≪≫ whiskerLeftIso G (pairε.symm ≪≫ β_ _ _) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso eb _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ eSucc.symm
  have hMNT : FibrewiseAlgEquivZero (M.tensor NT) := hM.tensor (hN.pullback tT)
  have hfibM :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
    k c ε g hg M hM r hr
  have hfibMN :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
    k c ε g hg (M.tensor NT) hMNT r hr
  have hfibMN1 :=
    RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
    k c ε g hg (M.tensor NT) hMNT (r + 1) (by omega)
  have h_a := RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso c t ea.symm (r + 1
    - g) hfibM
  have h_b := RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso c t eb.symm (r + 1
    - g) hfibMN
  have h_c : ∀ (k' : Type u) [Field k'] (s : Spec (CommRingCat.of k') ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s G)).H1 ∧
        Module.finrank k' (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s G)).H0 = r + 1 - g + 1
          := by
    have h := RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso c t ec.symm (r + 1
      + 1 - g) hfibMN1
    intro k' _ s 𝒲
    obtain ⟨h1, h0⟩ := h k' s 𝒲
    exact ⟨h1, by omega⟩
  obtain ⟨dP⟩ :=
    RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback k
    c ε h𝔉 t
    (rigSection c t P) (pullback.lift_snd _ _ _) G hG (r + 1 - g) h_a h_c
  obtain ⟨dε⟩ :=
    RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback k
    c ε h𝔉 t
    (rigSection c t ε) (pullback.lift_snd _ _ _) G hG (r + 1 - g) h_b h_c
  have detA : Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (G ⊗ IP.module)) ≅
      Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (F ⊗ Orε)) :=
    (Scheme.Modules.exteriorPower T (r + 1 - g)).mapIso ((Scheme.Modules.pushforward π).mapIso ea)
  have detB : Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (G ⊗ Iε.module)) ≅
      Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj ((M.tensor NT).L ⊗ Orε)) :=
    (Scheme.Modules.exteriorPower T (r + 1 - g)).mapIso ((Scheme.Modules.pushforward π).mapIso eb)
  let W : (pullback c (𝟙 S)).Modules := sectionTwist c ε (𝟙 S) r ⊗ sectionTwist c P (𝟙 S) 1
  have hW : Scheme.Modules.IsInvertible W :=
    ((isInvertible_sectionIdeal ε (𝟙 S)).pow r).isInvertible_invModule.tensor
      ((isInvertible_sectionIdeal P (𝟙 S)).pow 1).isInvertible_invModule
  let NW : RigidifiedLineBundle c ε (𝟙 S) := ofField W hW
  obtain ⟨bcεr⟩ := RelPicard.nonempty_pullback_sectionTwist_iso k c ε tT r
  have eW : Orε ⊗ OP ≅ (NW.pullbackAlong tT).L :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (bcεr ⊗ᵢ bcP)).symm
  have eG : G ≅ F ⊗ (NW.pullbackAlong tT).L := α_ _ _ _ ≪≫ whiskerLeftIso F eW
  obtain ⟨invP⟩ := RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
    NW P t
  obtain ⟨invε⟩ := RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
    NW ε t
  have pG : (Scheme.Modules.pullback (rigSection c t P)).obj G ≅ (Scheme.Modules.pullback
    (rigSection c t P)).obj F :=
    (Scheme.Modules.pullback _).mapIso eG ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      whiskerLeftIso _ invP ≪≫ ρ_ _
  have εG : (Scheme.Modules.pullback (rigSection c t ε)).obj G ≅ 𝟙_ _ :=
    (Scheme.Modules.pullback _).mapIso eG ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (M.rigidified.some ⊗ᵢ invε) ≪≫ λ_ _
  have eD : Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj ((M.tensor NT).L ⊗
    Orε)) ≅
      Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (F ⊗ Orε)) ⊗
        (Scheme.Modules.pullback (rigSection c t P)).obj F :=
    ((dε ≪≫ (detB ⊗ᵢ εG) ≪≫ ρ_ _).symm) ≪≫ dP ≪≫ (detA ⊗ᵢ pG)
  have hDM : Scheme.Modules.IsInvertible
      (Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (F ⊗ Orε))) :=
    Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank
      (RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre k c ε h𝔉 t (F ⊗ Orε) (hF.tensor
        hOrε) (r + 1 - g) hfibM)
  have hA : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (rigSection c t P)).obj F) :=
    hF.pullback _
  obtain ⟨dualT⟩ := Scheme.Modules.IsInvertible.dual_tensor hDM hA
  obtain ⟨-, ⟨pairA⟩⟩ := hA.dual
  refine ⟨whiskerRightIso (Scheme.Modules.dualMapIso eD ≪≫ dualT) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (β_ _ _ ≪≫ pairA) ≪≫ ρ_ _⟩
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
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
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
attribute [-simp]
  SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply exteriorPower.mulₗ_apply_coe
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.OModulePresheaf.prod_obj
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
attribute [-simp]
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
attribute [-simp]
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
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
attribute [-simp]
  AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
attribute [-simp]
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

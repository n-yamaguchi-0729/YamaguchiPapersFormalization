/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.JacobianVarieties.Picard.RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
import Nyll.JacobianVarieties.Picard.Exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
import Nyll.JacobianVarieties.Picard.RelEffCartierDiv_eq_pullbackAlong_of_twistModule_iso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_mul
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_isProper
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_isUniversal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Geometry.Picard.Nonempty_pullback_sectionTwist_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_mul_left_cancel
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset
import Nyll.JacobianVarieties.Picard.Exists_opens_range_subset_iff_forall_subsingleton_H1_fibre

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf

/-!
# An open Picard chart from relative effective Cartier divisors

Use a universal divisor and an auxiliary twist to construct a chart for fibrewise
algebraically trivial rigidified line bundles. The vanishing of fibre H¹ identifies
the chart locus, and uniqueness of divisors proves its pullback universal property.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.OpenChart
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
attribute [-instance]
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
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
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instFiniteResidue
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
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp]
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
attribute [-simp]
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
attribute [-simp]
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
attribute [-simp]
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
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
attribute [-simp]
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
  AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace ChartOne
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}}
    {g : T ⟶ S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g')
    (E : RelEffCartierDiv f l g') (hD : D.I = D₀.I * E.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (E.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * E.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mul]

theorem OverTotal_snd_eq_of_eq {Cat : Type*} [Category Cat] {S : Cat} {G : (Over S)ᵒᵖ ⥤ Type*}
    {T : Cat}
    {a b : G.OverTotal T} (h : a = b) :
    b.2 = G.map (Over.homMk (𝟙 T) (by rw [h]; exact Category.id_comp b.1)
      : Over.mk b.1 ⟶ Over.mk a.1).op a.2 := by
  subst h
  exact (Functor.map_op_apply_eq_self _ rfl _).symm

theorem RigidifiedLineBundle_pullbackAlong_L_eq {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) {ψ ψ' : SchemeHomOver t' t} (h : ψ.1 = ψ'.1) :
    (M.pullbackAlong ψ).L = (M.pullbackAlong ψ').L := by
  rw [Subtype.ext h]

section Separated

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
@[reassoc (attr := simp)]
theorem rigSection_snd' {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    rigSection c u ε ≫ pullback.snd c u = 𝟙 V :=
  pullback.lift_snd _ _ _

theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  have : SmoothOfRelativeDimension 1 (pullback.snd c u) :=
    _root_.AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd 1 c u
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c u)
    (rigSection c u ε) (rigSection_snd' R c ε u)

theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε u).pow n).isInvertible_invModule

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
/-- The rigidified line bundle tensored with the section twist and auxiliary divisor ideal. -/
abbrev Mγ {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) {V : Scheme.{u}}
    (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) : (pullback c u).Modules :=
  LV.L ⊗ (sectionTwist c ε u n ⊗ (Dγ.pullbackAlong u (Category.comp_id u)).idealModule)

theorem isInvertible_Mγ {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) :
    Scheme.Modules.IsInvertible (Mγ R c ε n Dγ u LV) :=
  LV.isInvertible.tensor ((isInvertible_sectionTwist R c ε u n).tensor
    (Dγ.pullbackAlong u (Category.comp_id u)).isInvertible_I.isInvertible_module)

section Transport

variable {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
  (ψ : SchemeHomOver t' t) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

/-- Identify the two fibres associated to a morphism over the base. -/
noncomputable def fibreIso
    : pullback (pullback.snd c t) (s' ≫ ψ.1) ≅ pullback (pullback.snd c t') s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ.1) ≪≫
    pullback.congrHom rfl (by rw [Category.assoc, ψ.2]) ≪≫ (pullbackLeftPullbackSndIso c t' s').symm

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem fibreIso_hom_fibreAt :
    (fibreIso R c t t' ψ s').hom ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem fibreIso_hom_fst_baseChangeSnd :
    (fibreIso R c t t' ψ s').hom ≫ pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s' ≫ ψ.1) := by
  have hβ : baseChangeSnd c ψ =
      pullback.lift (pullback.fst c t' ≫ 𝟙 C) (pullback.snd c t' ≫ ψ.1)
        (by rw [Category.comp_id, pullback.condition, Category.assoc, ψ.2]) := rfl
  rw [hβ]
  apply pullback.hom_ext
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem nonempty_Mγ_iso_pullback :
    Nonempty (Mγ R c ε n Dγ t' (L.pullbackAlong ψ) ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Mγ R c ε n Dγ t L)) := by
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 =
      Dγ.pullbackAlong t' (Category.comp_id _) :=
    (RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _).trans
      (pullbackAlong_congr_hom Dγ ψ.2 _ _)
  have hI : (Dγ.pullbackAlong t' (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
      (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong t' (Category.comp_id _)).idealModule := by
    have hcmp : IsIso
        ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison
          (baseChangeSnd c ψ)) :=
      Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
        (Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I
        (hI ▸ (Dγ.pullbackAlong t' (Category.comp_id _)).isInvertible_I)
    exact @asIso _ _ _ _
        ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison
          (baseChangeSnd c ψ)) hcmp ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  exact ⟨(Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso R c ε ψ n).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm⟩

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L) ≅
      (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).obj
        (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε n Dγ t t' ψ L
  exact ⟨((Scheme.Modules.pullbackCongr
      (fibreIso_hom_fst_baseChangeSnd R c t t' ψ s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t t' ψ s').hom
      (pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ)).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c t') s')
          (baseChangeSnd c ψ)).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

theorem fibre_transport_to_t (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ.1))
          (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t' s')
          (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε n Dγ t t' ψ L s'
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s' ≫ ψ.1)) (fibreAt c t' s') (fibreIso R c t t' ψ s')
      (fibreIso_hom_fibreAt R c t t' ψ s') 𝒲 _ _ eφ
  exact ⟨𝒱, h1⟩

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t' s')
          (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1))
          (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε n Dγ t t' ψ L s'
  let φ := fibreIso R c t t' ψ s'
  have hφ' : φ.symm.hom ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, fibreIso_hom_fibreAt]
  have e' := ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr φ.inv_hom_id).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso eφ.symm
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t' s') (fibreAt c t (s' ≫ ψ.1)) φ.symm hφ' 𝒲 _ _ e'
  exact ⟨𝒱, h1⟩

theorem forall_subsingleton_H1_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1))
          (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1)
    (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t' s')
        (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t R c ε n Dγ t t' ψ L s' 𝒲
  have := h 𝒱
  exact e1.symm.toEquiv.subsingleton

theorem forall_subsingleton_H1_of_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t' s')
          (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1)
    (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1))
        (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε n Dγ t t' ψ L s' 𝒲
  have := h 𝒱
  exact e1.symm.toEquiv.subsingleton

end Transport

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem forall_subsingleton_H1_of_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {F F' : (pullback c t).Modules} (i : F ≅ F') {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ T)
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H1 := by
  have e : fibreModule c t s F
      ≅ (Scheme.Modules.pullback (Iso.refl (pullback (pullback.snd c t) s)).hom).obj
      (fibreModule c t s F') :=
    (Scheme.Modules.pullback _).mapIso i ≪≫ ((Scheme.Modules.pullbackId _).app _).symm
  obtain ⟨𝒱, -, -, -, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (fibreAt c t s) (Iso.refl _) (Category.id_comp _) 𝒲 _ _ e
  have := h 𝒱
  exact h1.symm.toEquiv.subsingleton

variable (g e : ℕ) {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (DY : RelEffCartierDiv c (g + e) y)

/-- Rigidify the twist module of the universal effective divisor. -/
noncomputable def LY : RigidifiedLineBundle c ε y :=
  ⟨DY.twistModule c ε, (DY.isInvertible_twistModule_and_nonempty_pullback_iso c ε).1,
    (DY.isInvertible_twistModule_and_nonempty_pullback_iso c ε).2⟩

@[scoped simp] theorem LY_L : (LY R c ε g e y DY).L = DY.twistModule c ε := rfl

end Separated

section Chart

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

variable [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c]
  (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
  (g e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
  (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H1 = 1)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (𝒟 : RelEffCartierDiv c g y)
  (hU : 𝒟.IsUniversal)
  (DY : RelEffCartierDiv c (g + e) y)
  (hDY : DY.I = 𝒟.I * (Dγ.pullbackAlong y (Category.comp_id y)).I)


theorem fibrewiseAlgEquivZero_LY : FibrewiseAlgEquivZero (LY R c ε g e y DY) :=
  fun k _ _ s => DY.isAlgEquivZero_twistModule_fibre c ε k s

variable (UY : Y.Opens)
  (hUY : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Y),
    Set.range ⇑s ⊆ (UY : Set Y) ↔
      ∀ (𝒲 : (pullback (pullback.snd c y) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c y s)
            (fibreModule c y s (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY)))).H1)

/-- The algebraically trivial Picard class on the open chart locus. -/
noncomputable def chartElem :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op (UY : Scheme.{u})) :=
  ⟨UY.ι ≫ y, ⟨Quotient.mk _ ((LY R c ε g e y DY).pullbackAlong
      (⟨UY.ι, rfl⟩ : SchemeHomOver (UY.ι ≫ y) y)),
    (algEquivZeroCut c ε).pullback_mem _ _ _ _ (fibrewiseAlgEquivZero_LY R c ε g e y DY)⟩⟩

@[scoped simp] theorem chartElem_fst : (chartElem R c ε g e y DY UY).1 = UY.ι ≫ y := rfl

/-- The Yoneda morphism determined by the universal Picard class on the chart. -/
noncomputable def chartMap :
    uliftYoneda.{u + 1}.obj (UY : Scheme.{u})
      ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal :=
  uliftYonedaEquiv.{u + 1, u, u + 1}.symm (chartElem R c ε g e y DY UY)

@[scoped simp] theorem uliftYonedaEquiv_chartMap :
    uliftYonedaEquiv.{u + 1, u, u + 1} (chartMap R c ε g e y DY UY) = chartElem R c ε g e y DY UY :=
  Equiv.apply_symm_apply _ _

omit [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c] in
theorem uliftYonedaEquiv_uliftYoneda_map_comp {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} {T T' : Scheme.{u}}
    (ψ : T' ⟶ T)
    (f : uliftYoneda.{u + 1}.obj T ⟶ F) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map ψ ≫ f) =
      F.map ψ.op (uliftYonedaEquiv.{u + 1, u, u + 1} f) :=
  (uliftYonedaEquiv_naturality f ψ.op).symm

theorem uliftYonedaEquiv_map_comp_chartMap {T : Scheme.{u}} (φ' : T ⟶ (UY : Scheme.{u})) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε g e y DY UY) =
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.map φ'.op
        (chartElem R c ε g e y DY UY) := by
  rw [uliftYonedaEquiv_uliftYoneda_map_comp, uliftYonedaEquiv_chartMap]

omit [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c] in
/-- View a fibrewise algebraically trivial rigidified bundle as a total presheaf element. -/
def pointElem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op T) :=
  ⟨t, ⟨Quotient.mk _ L, hL⟩⟩

omit [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c] in
@[scoped simp] theorem pointElem_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) : (pointElem R c ε t L hL).1 = t := rfl

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t)
  (hL : FibrewiseAlgEquivZero L) (U : T.Opens)
  (hUiff : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
    Set.range ⇑s ⊆ (U : Set T) ↔
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s)
            (fibreModule c t s (Mγ R c ε (g + e) Dγ t L))).H1)
  (D : RelEffCartierDiv c (g + e) (U.ι ≫ t)) (D₀ : RelEffCartierDiv c g (U.ι ≫ t))
  (hD : D.I = D₀.I * (Dγ.pullbackAlong (U.ι ≫ t) (Category.comp_id _)).I)
  (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong
      (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L))

omit [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c]
    [LocallyOfFiniteType t] in
include hDY hD in
theorem D_eq_pullbackAlong_lift : D = DY.pullbackAlong (hU.lift D₀) (hU.lift_comp D₀) := by
  refine RelEffCartierDiv.ext ?_
  rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, hU.pullbackAlong_lift, RelEffCartierDiv.pullbackAlong_comp,
    pullbackAlong_congr_hom Dγ (hU.lift_comp D₀) _ (Category.comp_id _)]
  exact hD

omit [IsNoetherianRing R] [GeometricallyIntegral c] [LocallyOfFiniteType t] in
include hDY hD hDL in
theorem nonempty_LY_pullbackAlong_lift_iso :
    Nonempty (((LY R c ε g e y DY).pullbackAlong
        (⟨hU.lift D₀, hU.lift_comp D₀⟩ : SchemeHomOver (U.ι ≫ t) y)).L ≅
      (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t)).L) := by
  obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε
    (⟨hU.lift D₀, hU.lift_comp D₀⟩ : SchemeHomOver (U.ι ≫ t) y) DY
  exact ⟨i.symm ≪≫ eqToIso (congrArg (fun D' => RelEffCartierDiv.twistModule c ε D')
    (D_eq_pullbackAlong_lift R c g e Dγ y 𝒟 hU DY hDY t U D D₀ hD).symm) ≪≫ hDL.some⟩

omit [IsNoetherianRing R] [GeometricallyIntegral c] [LocallyOfFiniteType t] in
include hUiff in
theorem subsingleton_H1_U (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (U.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (U.ι ≫ t) s) (fibreModule c (U.ι ≫ t) s
      (Mγ R c ε (g + e) Dγ (U.ι ≫ t)
          (L.pullbackAlong (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t))))).H1 := by
  have hrange : Set.range ⇑(s ≫ U.ι) ⊆ (U : Set T) := by
    rw [← Scheme.Opens.range_ι U]
    rintro _ ⟨x, rfl⟩
    exact ⟨s x, (Scheme.Hom.comp_apply s U.ι x).symm⟩
  exact forall_subsingleton_H1_pullbackAlong R c ε (g + e) Dγ t (U.ι ≫ t) ⟨U.ι, rfl⟩ L s
    ((hUiff k (s ≫ U.ι)).1 hrange) 𝒲

omit [IsNoetherianRing R] [GeometricallyIntegral c] [LocallyOfFiniteType t] in
include hDY hUiff hD hDL in
theorem subsingleton_H1_U' (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (U.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (U.ι ≫ t) s) (fibreModule c (U.ι ≫ t) s
      (Mγ R c ε (g + e) Dγ (U.ι ≫ t)
        ((LY R c ε g e y DY).pullbackAlong
            (⟨hU.lift D₀, hU.lift_comp D₀⟩ : SchemeHomOver (U.ι ≫ t) y))))).H1 := by
  obtain ⟨i⟩ := nonempty_LY_pullbackAlong_lift_iso R c ε g e Dγ y 𝒟 hU DY hDY t L U D D₀ hD hDL
  exact forall_subsingleton_H1_of_iso R c (U.ι ≫ t) (i.symm ⊗ᵢ Iso.refl _) s
    (subsingleton_H1_U R c ε g e Dγ t L U hUiff k s) 𝒲

omit [IsNoetherianRing R] [GeometricallyIntegral c] [LocallyOfFiniteType t] in
include hDY hUY hUiff hD hDL in
theorem range_lift_subset : Set.range ⇑(hU.lift D₀) ⊆ (UY : Set Y) := by
  rintro _ ⟨p, rfl⟩
  have key := (hUY ((U : Scheme.{u}).residueField p)
    ((U : Scheme.{u}).fromSpecResidueField p ≫ hU.lift D₀)).2
    (fun 𝒲 => forall_subsingleton_H1_of_pullbackAlong R c ε (g + e) Dγ y (U.ι ≫ t)
      ⟨hU.lift D₀, hU.lift_comp D₀⟩ (LY R c ε g e y DY) ((U : Scheme.{u}).fromSpecResidueField p)
      (subsingleton_H1_U' R c ε g e Dγ y 𝒟 hU DY hDY t L U hUiff D D₀ hD hDL _
        ((U : Scheme.{u}).fromSpecResidueField p)) 𝒲)
  have hp : p ∈ Set.range ⇑((U : Scheme.{u}).fromSpecResidueField p) := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.mem_singleton p
  obtain ⟨q, hq⟩ := hp
  exact key ⟨q, (Scheme.Hom.comp_apply _ _ q).trans (congrArg (hU.lift D₀) hq)⟩

omit [IsNoetherianRing R] [GeometricallyIntegral c] [LocallyOfFiniteType t] in
/-- Factor the universal divisor lift through the open chart locus. -/
noncomputable def φ : (U : Scheme.{u}) ⟶ (UY : Scheme.{u}) :=
  IsOpenImmersion.lift UY.ι (hU.lift D₀)
    (by rw [Scheme.Opens.range_ι]
      ; exact range_lift_subset R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL)

omit [IsNoetherianRing R] [GeometricallyIntegral c] [LocallyOfFiniteType t] in
@[reassoc (attr := simp)]
theorem φ_ι : φ R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL ≫ UY.ι = hU.lift D₀ :=
  IsOpenImmersion.lift_fac _ _ _

omit [SmoothOfRelativeDimension 1 c] [IsNoetherianRing R] [IsProper c] [GeometricallyIntegral c]
    [LocallyOfFiniteType t] in
include hUiff in
theorem clause_i (L' : RigidifiedLineBundle c ε t) (hL' : Nonempty (L'.L ≅ L.L))
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Set.range ⇑s ⊆ (U : Set T) ↔
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s)
            (fibreModule c t s (Mγ R c ε (g + e) Dγ t L'))).H1 := by
  refine (hUiff k s).trans ⟨fun h 𝒲 => ?_, fun h 𝒲 => ?_⟩
  · exact forall_subsingleton_H1_of_iso R c t (hL'.some.symm ⊗ᵢ Iso.refl _) s h 𝒲
  · exact forall_subsingleton_H1_of_iso R c t (hL'.some ⊗ᵢ Iso.refl _) s h 𝒲

omit [LocallyOfFiniteType t] in
theorem clause_ii :
    uliftYoneda.{u + 1}.map (φ R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL) ≫
        chartMap R c ε g e y DY UY =
      uliftYoneda.{u + 1}.map U.ι ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm
        (pointElem R c ε t L hL) := by
  apply uliftYonedaEquiv.{u + 1, u, u + 1}.injective
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp,
    Equiv.apply_symm_apply]
  refine Functor.OverTotal.ext' ?_ ?_
  · change φ R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL ≫ UY.ι ≫ y = U.ι ≫ t
    rw [φ_ι_assoc, hU.lift_comp]
  · apply Subtype.ext
    refine Quotient.sound ⟨?_⟩
    refine RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ ?_) ≪≫
      (nonempty_LY_pullbackAlong_lift_iso R c ε g e Dγ y 𝒟 hU DY hDY t L U D D₀ hD hDL).some
    simp only [postComp, Category.assoc]
    change (𝟙 (U : Scheme.{u})) ≫
      φ R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL ≫ UY.ι = hU.lift D₀
    rw [Category.id_comp]
    exact φ_ι R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL

include h𝔉 hχ in
theorem clause_iii {T' : Scheme.{u}} (ψ : T' ⟶ T) (φ' : T' ⟶ (UY : Scheme.{u}))
    [LocallyOfFiniteType (ψ ≫ t)]
    (hφ' : uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε g e y DY UY =
      uliftYoneda.{u + 1}.map ψ ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm
        (pointElem R c ε t L hL)) :
    ∃ χ : T' ⟶ (U : Scheme.{u}), χ ≫ U.ι = ψ ∧
      χ ≫ φ R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL = φ' := by
  have E := congrArg uliftYonedaEquiv.{u + 1, u, u + 1} hφ'
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp,
    Equiv.apply_symm_apply] at E
  have h1 : (φ' ≫ UY.ι) ≫ y = ψ ≫ t := by
    have := congrArg Sigma.fst E
    rw [Functor.overTotal_map_fst, Functor.overTotal_map_fst] at this
    exact (Category.assoc φ' UY.ι y).trans this
  let Ψ : SchemeHomOver (ψ ≫ t) t := ⟨ψ, rfl⟩
  let Φ : SchemeHomOver (ψ ≫ t) y := ⟨φ' ≫ UY.ι, h1⟩
  have eL : Nonempty ((L.pullbackAlong Ψ).L ≅ ((LY R c ε g e y DY).pullbackAlong Φ).L) := by
    have h2 := OverTotal_snd_eq_of_eq E
    obtain ⟨i⟩ := Quotient.exact (congrArg Subtype.val h2)
    exact ⟨i ≪≫ RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ (by
        simp only [postComp, Φ, Category.assoc]
        exact Category.id_comp _))⟩
  have hD' : (DY.pullbackAlong (φ' ≫ UY.ι) h1).I =
      (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ h1 _ (Category.comp_id _)]
  have hD'L : Nonempty ((DY.pullbackAlong (φ' ≫ UY.ι) h1).twistModule c ε
      ≅ (L.pullbackAlong Ψ).L) := by
    obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε Φ DY
    exact ⟨i ≪≫ eL.some.symm⟩
  have h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c (ψ ≫ t)) s').TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (ψ ≫ t) s') (fibreModule c (ψ ≫ t) s'
        (Mγ R c ε (g + e) Dγ (ψ ≫ t) (L.pullbackAlong Ψ)))).H1 := by
    intro k _ s' 𝒲
    have hrange : Set.range ⇑(s' ≫ φ' ≫ UY.ι) ⊆ (UY : Set Y) := by
      rw [← Scheme.Opens.range_ι UY]
      rintro _ ⟨z, rfl⟩
      exact ⟨φ' (s' z), ((Scheme.Hom.comp_apply s' (φ' ≫ UY.ι) z).trans
        (Scheme.Hom.comp_apply φ' UY.ι (s' z))).symm⟩
    have hY := (hUY k (s' ≫ φ' ≫ UY.ι)).1 hrange
    have hT' := forall_subsingleton_H1_pullbackAlong R c ε (g + e) Dγ y (ψ ≫ t) Φ
      (LY R c ε g e y DY) s' hY
    exact forall_subsingleton_H1_of_iso R c (ψ ≫ t) (eL.some.symm ⊗ᵢ Iso.refl _) s' hT' 𝒲
  obtain ⟨hrangeU, huniq⟩ :=
    relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso R c ε h𝔉 g e (g + e) rfl Dγ hχ
    t L hL U (fun k _ s h => (hUiff k s).2 h) D D₀ hD hDL (ψ ≫ t) Ψ
    (DY.pullbackAlong (φ' ≫ UY.ι) h1) (𝒟.pullbackAlong (φ' ≫ UY.ι) h1) hD' hD'L h1'
  have hrangeU' : Set.range ⇑ψ ⊆ Set.range ⇑U.ι := by rw [Scheme.Opens.range_ι]; exact hrangeU
  refine ⟨IsOpenImmersion.lift U.ι ψ hrangeU', IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have hχt : IsOpenImmersion.lift U.ι ψ hrangeU' ≫ U.ι ≫ t = ψ ≫ t := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
  have hDD := huniq (IsOpenImmersion.lift U.ι ψ hrangeU') (IsOpenImmersion.lift_fac _ _ _)
  have hI : (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I =
      (D₀.pullbackAlong (IsOpenImmersion.lift U.ι ψ hrangeU') hχt).I *
        (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [← hD', hDD, pullbackAlong_I_eq_mul D D₀ _ hD _ hχt, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ hχt _ (Category.comp_id _)]
  have hI' : (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I
      = (D₀.pullbackAlong (IsOpenImmersion.lift U.ι ψ hrangeU') hχt).I := by
    rw [mul_comm, mul_comm (D₀.pullbackAlong _ hχt).I] at hI
    exact (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).isInvertible_I.mul_left_cancel hI
  have e1 : φ' ≫ UY.ι = hU.lift (𝒟.pullbackAlong (φ' ≫ UY.ι) h1) :=
    hU.eq_lift h1 (pullsBackOver_pullbackAlong 𝒟 (φ' ≫ UY.ι) h1)
  have e2 : IsOpenImmersion.lift U.ι ψ hrangeU' ≫ hU.lift D₀
      = hU.lift (𝒟.pullbackAlong (φ' ≫ UY.ι) h1) := by
    refine hU.eq_lift (by rw [Category.assoc, hU.lift_comp, hχt]) ?_
    change (𝒟.pullbackAlong (IsOpenImmersion.lift U.ι ψ hrangeU' ≫ hU.lift D₀) _).I
      = (𝒟.pullbackAlong (φ' ≫ UY.ι) h1).I
    rw [hI', ← RelEffCartierDiv.pullbackAlong_comp 𝒟 (hU.lift D₀) (hU.lift_comp D₀) _ hχt,
      hU.pullbackAlong_lift]
  rw [← cancel_mono UY.ι, Category.assoc, φ_ι, e2, ← e1]

end Chart

end AlgebraicGeometry.RelPicard.ChartOne

open AlgebraicGeometry.RelPicard.ChartOne in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1) :
    ∃ (X : Scheme.{u})
      (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧
      ∀ ⦃T : Scheme.{u}⦄
        (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1),
              Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U : Set T) ↔
                ∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s)
                      (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1
                          (Category.comp_id _)).idealModule)))).H1) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U, χ ≫ U.ι = ψ ∧ χ ≫ φ = φ' := by
  subst hr
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨Y, y, 𝒟, hU⟩ :=
    RelEffCartierDiv.exists_isUniversal c 𝔉.exists_isAffineOpen_le_preimage_of_finset g
  have : IsProper y := hU.isProper
  obtain ⟨DY, hDY⟩ := RelEffCartierDiv.exists_I_eq_mul 𝒟 (Dγ.pullbackAlong y (Category.comp_id y))
  obtain ⟨UY, hUY⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 y
    (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY)) (isInvertible_Mγ R c ε (g + e) Dγ y _)
  refine ⟨UY, chartMap R c ε g e y DY UY, ?_, ?_⟩
  · rw [uliftYonedaEquiv_chartMap]
    change LocallyOfFiniteType (UY.ι ≫ y)
    infer_instance
  intro T x hx
  generalize hxa : uliftYonedaEquiv x = a at hx ⊢
  obtain rfl : x = uliftYonedaEquiv.symm a := by rw [← hxa, Equiv.symm_apply_apply]
  clear hxa
  change (relSubPicPresheaf c ε (algEquivZeroCut c ε)).OverTotal T at a
  obtain ⟨t, ⟨ξ, hξ⟩⟩ := a
  obtain ⟨L, rfl⟩ := Quotient.exists_rep ξ
  change FibrewiseAlgEquivZero L at hξ
  have : LocallyOfFiniteType t := hx
  change ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ UY), _ ∧
    uliftYoneda.{u + 1}.map φ ≫ _ = uliftYoneda.{u + 1}.map U.ι ≫
      uliftYonedaEquiv.symm (pointElem R c ε t L hξ) ∧ _
  obtain ⟨U, hUiff⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 t
    (Mγ R c ε (g + e) Dγ t L) (isInvertible_Mγ R c ε (g + e) Dγ t L)
  obtain ⟨D, D₀, hD, hDL⟩ :=
    exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1 R c ε h𝔉 g e (g + e) rfl
    Dγ hχ t L hξ U (fun k _ s hs => (hUiff k s).1 hs)
  refine ⟨U, φ R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L U hUiff D D₀ hD hDL, ?_, ?_, ?_⟩
  · intro L' hL' k _ s
    exact clause_i R c ε g e Dγ t L U hUiff L' (Quotient.exact hL') k s
  · exact clause_ii R c ε g e Dγ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL
  · intro T' ψ φ' hlft hφ'
    have := hlft
    exact clause_iii R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL ψ φ' hφ'
end
end JacobianVarieties.Picard.Proofs.OpenChart
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
  PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
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
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
attribute [-instance]
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
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
  ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
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
attribute [-instance]
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
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp]
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp
  AlgebraicGeometry.RelEffCartierDiv.functor_map_fst
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
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
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
attribute [-simp]
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
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
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
attribute [-simp]
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst

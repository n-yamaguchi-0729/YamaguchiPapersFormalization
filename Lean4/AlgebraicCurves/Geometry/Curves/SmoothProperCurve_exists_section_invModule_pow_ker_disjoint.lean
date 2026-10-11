/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_section_invModule_pow_ker_disjoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Fintype.Card
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import SchemeTheory.Modules.PullbackLocalSection
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Cohomology.Adelic.Index
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.RelativeSectionTwist
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Models.Exists_isAffineOpen_forall_mem_of_finset
import AlgebraicCurves.Models.Exists_isAffineOpen_sup_eq_top
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_section_invModule_pow_ker_notMem_support_of_isMaximal
import AlgebraicCurves.Geometry.Picard.Nonempty_pullback_sectionTwist_iso
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_subsingleton_H1_and_finrank_H0_sectionsOf_pullback_invModule_pow_ker
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import AlgebraicCurves.Cohomology.Sheaves.Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_subsingleton_HSucc_zero_ofModules_of_subsingleton
import AlgebraicCurves.Cohomology.Cech.OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_ideal_comap_of_le
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection

/-! Sections of an inverse ideal power disjoint from the marked section. -/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_section_invModule_pow_ker_disjoint
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
attribute [-instance] AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
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
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
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
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
attribute [-instance] AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
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
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
attribute [-simp] AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
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
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
attribute [-simp] AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
attribute [-simp] AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
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
  AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
attribute [-simp] GoodReductionJacobian.schemeHomOverComp_coe
  NeronModelInfra.schemeHomOverEquivOverHom_apply
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
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
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

noncomputable section

universe u

open _root_.CategoryTheory
open _root_.Opposite
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) {c : X ⟶ Spec (.of
  R)}
variable (F : OModulePresheaf c)

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme

local notation "K" => 𝒱.toOrderedAffineCover

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.idx0 (i : ULift.{u} (Fin 2)) :
  (K).Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by omega)⟩

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

private def _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.idx01 : (K).Idx 1 :=
  ⟨fun j => ⟨j⟩, fun a b h => by
    change (⟨a⟩ : ULift.{u} (Fin 2)) < ⟨b⟩
    exact h⟩

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
theorem idx0_val (i : ULift.{u} (Fin 2)) (j : Fin 1) : (𝒱.idx0 i).1 j = i := rfl

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.eq_idx0 (s : (K).Idx 0) : s =
  𝒱.idx0 (s.1 0) :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

/-- The equivalence between degree zero cochain indices and the two affine charts. -/
def idxZeroEquiv : (K).Idx 0 ≃ ULift.{u} (Fin 2) where
  toFun s := s.1 0
  invFun := 𝒱.idx0
  left_inv s := (𝒱.eq_idx0 s).symm
  right_inv _ := rfl

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.eq_idx01 (s : (K).Idx 1) : s =
  𝒱.idx01 := by
  apply Subtype.ext; funext j
  have hs := s.2
  have h01 : s.1 0 < s.1 1 := hs (by decide)
  have hlt : (s.1 0).down < (s.1 1).down := h01
  have h0 : (s.1 0).down = 0 := by omega
  have h1 : (s.1 1).down = 1 := by omega
  fin_cases j
  · exact ULift.ext h0
  · exact ULift.ext h1

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
scoped instance uniqueIdxOne : Unique ((K).Idx 1) where
  default := 𝒱.idx01
  uniq := 𝒱.eq_idx01

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.isEmpty_Idx_add_two (i : ℕ) :
  IsEmpty ((K).Idx (i + 2)) := by
  rw [Scheme.OrderedAffineCover.Idx, isEmpty_subtype]
  intro s hs
  have := Fintype.card_le_of_injective s hs.injective
  simp only [Fintype.card_fin] at this
  change i + 2 + 1 ≤ Fintype.card (ULift.{u} (Fin 2)) at this
  rw [Fintype.card_ulift, Fintype.card_fin] at this
  omega

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_idx0 (i : ULift.{u} (Fin
  2)) : (K).inter (𝒱.idx0 i) = (K).U i :=
  le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_idx01 : (K).inter 𝒱.idx01
  = 𝒱.U0 ⊓ 𝒱.U1 :=
  le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
    (le_iInf fun j => by fin_cases j <;> [exact inf_le_left; exact inf_le_right])

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
end Scheme.TwoAffineOpenCover

namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf hiding Hom prod pow ker zero

private def _root_.AlgebraicGeometry.OModulePresheaf.resEq {U U' : X.Opens} (h : U = U') : F.obj U'
  ≃ₗ[R] F.obj U where
  toLinearMap := F.res h.le
  invFun := F.res h.ge
  left_inv x := by
    change F.res h.ge (F.res h.le x) = x
    exact (F.res_res _ _ _).trans (F.res_refl_apply _ x)
  right_inv x := by
    change F.res h.le (F.res h.ge x) = x
    exact (F.res_res _ _ _).trans (F.res_refl_apply _ x)

open _root_.AlgebraicGeometry.OModulePresheaf
theorem resEq_apply {U U' : X.Opens} (h : U = U') (x : F.obj U') : F.resEq h x = F.res h.le x := rfl

theorem res_resEq {U U' W : X.Opens} (h : U = U') (hW : W ≤ U) (x : F.obj U') :
    F.res hW (F.resEq h x) = F.res (hW.trans h.le) x := by
  rw [resEq_apply, F.res_res]

local notation "K" => 𝒱.toOrderedAffineCover

private def _root_.AlgebraicGeometry.OModulePresheaf.pick (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : ∀ i :
  ULift.{u} (Fin 2), F.obj ((K).U i)
  | ⟨⟨0, _⟩⟩ => p.1
  | ⟨⟨1, _⟩⟩ => p.2

open _root_.AlgebraicGeometry.OModulePresheaf
theorem pick_zero (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : F.pick 𝒱 p ⟨0⟩ = p.1 := rfl
theorem pick_one (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) : F.pick 𝒱 p ⟨1⟩ = p.2 := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.pick_add (p q : F.obj 𝒱.U0 × F.obj 𝒱.U1)
  (i : ULift.{u} (Fin 2)) :
    F.pick 𝒱 (p + q) i = F.pick 𝒱 p i + F.pick 𝒱 q i := by
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · rfl
  · rfl
  · omega

open _root_.AlgebraicGeometry.OModulePresheaf
private theorem _root_.AlgebraicGeometry.OModulePresheaf.pick_smul (r : R) (p : F.obj 𝒱.U0 × F.obj
  𝒱.U1) (i : ULift.{u} (Fin 2)) :
    F.pick 𝒱 (r • p) i = r • F.pick 𝒱 p i := by
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · rfl
  · rfl
  · omega

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.pickₗ (i : ULift.{u} (Fin 2)) : F.obj 𝒱.U0 ×
  F.obj 𝒱.U1 →ₗ[R] F.obj ((K).U i) where
  toFun p := F.pick 𝒱 p i
  map_add' p q := F.pick_add 𝒱 p q i
  map_smul' r p := F.pick_smul 𝒱 r p i

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroTo : F.cochain K 0 →ₗ[R] F.obj 𝒱.U0
  × F.obj 𝒱.U1 :=
  ((F.resEq (𝒱.inter_idx0 ⟨0⟩)).symm.toLinearMap.comp (LinearMap.proj (𝒱.idx0 ⟨0⟩))).prod
    ((F.resEq (𝒱.inter_idx0 ⟨1⟩)).symm.toLinearMap.comp (LinearMap.proj (𝒱.idx0 ⟨1⟩)))

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroOf : F.obj 𝒱.U0 × F.obj 𝒱.U1 →ₗ[R]
  F.cochain K 0 :=
  LinearMap.pi fun s => (F.res ((K).inter_le s 0)).comp (F.pickₗ 𝒱 (s.1 0))

open _root_.AlgebraicGeometry.OModulePresheaf
theorem cochainZeroTo_apply (f : F.cochain K 0) :
    F.cochainZeroTo 𝒱 f
      = (F.res (𝒱.inter_idx0 ⟨0⟩).ge (f (𝒱.idx0 ⟨0⟩)), F.res (𝒱.inter_idx0 ⟨1⟩).ge (f (𝒱.idx0
        ⟨1⟩))) :=
  rfl

theorem cochainZeroOf_apply (p : F.obj 𝒱.U0 × F.obj 𝒱.U1) (s : (K).Idx 0) :
    F.cochainZeroOf 𝒱 p s = F.res ((K).inter_le s 0) (F.pick 𝒱 p (s.1 0)) := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroTo_cochainZeroOf (p : F.obj
  𝒱.U0 × F.obj 𝒱.U1) :
    F.cochainZeroTo 𝒱 (F.cochainZeroOf 𝒱 p) = p := by
  rw [cochainZeroTo_apply]
  refine Prod.ext ?_ ?_
  · change F.res _ (F.res _ (F.pick 𝒱 p ⟨0⟩)) = p.1
    exact (F.res_res _ _ _).trans ((F.res_refl_apply _ _).trans (pick_zero 𝒱 F p))
  · change F.res _ (F.res _ (F.pick 𝒱 p ⟨1⟩)) = p.2
    exact (F.res_res _ _ _).trans ((F.res_refl_apply _ _).trans (pick_one 𝒱 F p))

open _root_.AlgebraicGeometry.OModulePresheaf
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroOf_cochainZeroTo (f : F.cochain
  K 0) :
    F.cochainZeroOf 𝒱 (F.cochainZeroTo 𝒱 f) = f := by
  funext s
  rw [cochainZeroOf_apply, cochainZeroTo_apply]
  obtain ⟨i, rfl⟩ : ∃ i, s = 𝒱.idx0 i := ⟨_, 𝒱.eq_idx0 s⟩
  rcases i with ⟨⟨_ | _ | n, hn⟩⟩
  · change F.res _ (F.res _ (f _)) = f _
    exact (F.res_res _ _ _).trans (F.res_refl_apply _ _)
  · change F.res _ (F.res _ (f _)) = f _
    exact (F.res_res _ _ _).trans (F.res_refl_apply _ _)
  · omega

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.cochainZeroEquiv : F.cochain K 0 ≃ₗ[R] F.obj
  𝒱.U0 × F.obj 𝒱.U1 :=
  LinearEquiv.ofLinearMap (F.cochainZeroTo 𝒱) (F.cochainZeroOf 𝒱)
    (LinearMap.ext (F.cochainZeroTo_cochainZeroOf 𝒱)) (LinearMap.ext (F.cochainZeroOf_cochainZeroTo
      𝒱))

open _root_.AlgebraicGeometry.OModulePresheaf

private theorem _root_.AlgebraicGeometry.OModulePresheaf.finite_HSucc_succ (i : ℕ) : Module.Finite
  R (F.HSucc K (i + 1)) := by
  have := 𝒱.isEmpty_Idx_add_two i
  have : Subsingleton (F.cochain K (i + 1 + 1)) := inferInstance
  have : Subsingleton (F.HSucc K (i + 1)) := Quot.Subsingleton
  exact Module.Finite.of_finite

open _root_.AlgebraicGeometry.OModulePresheaf
end OModulePresheaf

end AlgebraicGeometry

end

noncomputable section

namespace TwoChartCech
open _root_.TwoChartCech
open _root_.TwoChartCech

universe uR uK uC

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

universe u

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) {c : X ⟶ Spec (.of
  R)}
variable (F : OModulePresheaf c)

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme

local notation "K" => 𝒱.toOrderedAffineCover

private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.face_idx01_zero : (K).face
  𝒱.idx01 0 = 𝒱.idx0 ⟨1⟩ :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.face_idx01_one : (K).face
  𝒱.idx01 1 = 𝒱.idx0 ⟨0⟩ :=
  Subtype.ext (funext fun j => by fin_cases j; rfl)

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inter_le_inf (s : (K).Idx 1) :
  (K).inter s ≤ 𝒱.U0 ⊓ 𝒱.U1 := by
  rw [𝒱.eq_idx01 s, 𝒱.inter_idx01]

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
private theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.inf_le_inter (s : (K).Idx 1) :
  𝒱.U0 ⊓ 𝒱.U1 ≤ (K).inter s := by
  rw [𝒱.eq_idx01 s, 𝒱.inter_idx01]

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
end Scheme.TwoAffineOpenCover

namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf hiding Hom prod pow ker zero

local notation "K" => 𝒱.toOrderedAffineCover

private theorem _root_.AlgebraicGeometry.OModulePresheaf.res_congr_idx {i : ℕ} (co : F.cochain K i)
  {s s' : (K).Idx i} (e : s = s') {W : X.Opens}
    (p : W ≤ (K).inter s) (p' : W ≤ (K).inter s') : F.res p (co s) = F.res p' (co s') := by
  subst e; rfl

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo : F.cochain K 1 →ₗ[R] F.obj (𝒱.U0
  ⊓ 𝒱.U1) :=
  (F.res (𝒱.inf_le_inter 𝒱.idx01)).comp (LinearMap.proj 𝒱.idx01)

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneOf : F.obj (𝒱.U0 ⊓ 𝒱.U1) →ₗ[R]
  F.cochain K 1 :=
  LinearMap.pi fun s => F.res (𝒱.inter_le_inf s)

open _root_.AlgebraicGeometry.OModulePresheaf
theorem cochainOneTo_apply (co : F.cochain K 1) :
    F.cochainOneTo 𝒱 co = F.res (𝒱.inf_le_inter 𝒱.idx01) (co 𝒱.idx01) := rfl

theorem cochainOneOf_apply (x : F.obj (𝒱.U0 ⊓ 𝒱.U1)) (s : (K).Idx 1) :
    F.cochainOneOf 𝒱 x s = F.res (𝒱.inter_le_inf s) x := rfl

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo_cochainOneOf (x : F.obj (𝒱.U0
  ⊓ 𝒱.U1)) :
    F.cochainOneTo 𝒱 (F.cochainOneOf 𝒱 x) = x := by
  rw [cochainOneTo_apply, cochainOneOf_apply, F.res_res]
  exact F.res_refl_apply _ x

open _root_.AlgebraicGeometry.OModulePresheaf
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneOf_cochainOneTo (co : F.cochain
  K 1) :
    F.cochainOneOf 𝒱 (F.cochainOneTo 𝒱 co) = co := by
  funext s
  rw [cochainOneOf_apply, cochainOneTo_apply, F.res_res]
  have hs := 𝒱.eq_idx01 s
  subst hs
  exact F.res_refl_apply _ _

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.cochainOneEquiv : F.cochain K 1 ≃ₗ[R] F.obj
  (𝒱.U0 ⊓ 𝒱.U1) :=
  LinearEquiv.ofLinearMap (F.cochainOneTo 𝒱) (F.cochainOneOf 𝒱)
    (LinearMap.ext (F.cochainOneTo_cochainOneOf 𝒱)) (LinearMap.ext (F.cochainOneOf_cochainOneTo 𝒱))

open _root_.AlgebraicGeometry.OModulePresheaf

private theorem _root_.AlgebraicGeometry.OModulePresheaf.cochainOneTo_d (co : F.cochain K 0) :
    F.cochainOneTo 𝒱 (F.d K 0 co) = (F.twoChartSections 𝒱).cechDiff (F.cochainZeroTo 𝒱 co) := by
  rw [cochainOneTo_apply, F.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, ← sub_eq_add_neg,
    map_sub]
  refine Eq.trans ?_
    (TwoChartCech.Sections.cechDiff_apply (F.twoChartSections 𝒱) (F.cochainZeroTo 𝒱 co)).symm
  change F.res _ (F.res _ (co ((K).face 𝒱.idx01 0))) - F.res _ (F.res _ (co ((K).face 𝒱.idx01 1)))
    = F.res (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) (F.res _ (co (𝒱.idx0 ⟨1⟩)))
      - F.res (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) (F.res _ (co (𝒱.idx0 ⟨0⟩)))
  apply congrArg₂ (fun x y : F.obj (𝒱.U0 ⊓ 𝒱.U1) => x - y)
  · exact (F.res_res _ _ _).trans
      ((F.res_congr_idx 𝒱 co 𝒱.face_idx01_zero _
        ((inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1).trans (𝒱.inter_idx0 ⟨1⟩).ge)).trans
          (F.res_res _ _ _).symm)
  · exact (F.res_res _ _ _).trans
      ((F.res_congr_idx 𝒱 co 𝒱.face_idx01_one _
        ((inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0).trans (𝒱.inter_idx0 ⟨0⟩).ge)).trans
          (F.res_res _ _ _).symm)

open _root_.AlgebraicGeometry.OModulePresheaf
private theorem _root_.AlgebraicGeometry.OModulePresheaf.cechDiff_comp_cochainZeroEquiv :
    (F.twoChartSections 𝒱).cechDiff ∘ₗ (F.cochainZeroEquiv 𝒱).toLinearMap
      = (F.cochainOneEquiv 𝒱).toLinearMap ∘ₗ F.d K 0 := by
  apply LinearMap.ext
  intro co
  exact (F.cochainOneTo_d 𝒱 co).symm

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.H0Equiv : F.H0 K ≃ₗ[R] (F.twoChartSections
  𝒱).H0 :=
  LinearEquiv.ofBijective _
    (TwoChartCech.kerMap_bijective_of_bijective (F.d K 0) (F.twoChartSections 𝒱).cechDiff
      (F.cochainZeroEquiv 𝒱).toLinearMap (F.cochainOneEquiv 𝒱).toLinearMap
      (F.cechDiff_comp_cochainZeroEquiv 𝒱) (F.cochainZeroEquiv 𝒱).bijective
      (F.cochainOneEquiv 𝒱).injective)

open _root_.AlgebraicGeometry.OModulePresheaf
private theorem _root_.AlgebraicGeometry.OModulePresheaf.d_one_eq_zero : F.d K 1 = 0 := by
  have := 𝒱.isEmpty_Idx_add_two 0
  apply LinearMap.ext
  intro co
  exact Subsingleton.elim _ _

open _root_.AlgebraicGeometry.OModulePresheaf
private theorem _root_.AlgebraicGeometry.OModulePresheaf.ker_d_one_eq_top : LinearMap.ker (F.d K 1)
  = ⊤ := by
  rw [F.d_one_eq_zero 𝒱, LinearMap.ker_zero]

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquivCoker : F.HSucc K 0 ≃ₗ[R]
  (F.cochain K 1 ⧸ LinearMap.range (F.d K 0)) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop _ (F.ker_d_one_eq_top 𝒱)) (by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy
    · intro y hy
      refine ⟨⟨y, by rw [F.ker_d_one_eq_top 𝒱]; trivial⟩, hy, rfl⟩)

open _root_.AlgebraicGeometry.OModulePresheaf

private def _root_.AlgebraicGeometry.OModulePresheaf.HSuccZeroEquiv : F.HSucc K 0 ≃ₗ[R]
  (F.twoChartSections 𝒱).H1 :=
  (F.HSuccZeroEquivCoker 𝒱).trans (LinearEquiv.ofBijective _
    (TwoChartCech.cokerMap_bijective_of_bijective (F.d K 0) (F.twoChartSections 𝒱).cechDiff
      (F.cochainZeroEquiv 𝒱).toLinearMap (F.cochainOneEquiv 𝒱).toLinearMap
      (F.cechDiff_comp_cochainZeroEquiv 𝒱) (F.cochainZeroEquiv 𝒱).surjective
      (F.cochainOneEquiv 𝒱).bijective))

open _root_.AlgebraicGeometry.OModulePresheaf

theorem cechFinite_toOrderedAffineCover_iff' :
    F.CechFinite K ↔
      Module.Finite R (F.twoChartSections 𝒱).H0 ∧ Module.Finite R (F.twoChartSections 𝒱).H1 := by
  constructor
  · rintro ⟨h0, hS⟩
    exact ⟨Module.Finite.equiv (F.H0Equiv 𝒱), by
      have := hS 0; exact Module.Finite.equiv (F.HSuccZeroEquiv 𝒱)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Module.Finite.equiv (F.H0Equiv 𝒱).symm, fun i => ?_⟩
    cases i with
    | zero => exact Module.Finite.equiv (F.HSuccZeroEquiv 𝒱).symm
    | succ i => exact F.finite_HSucc_succ 𝒱 i

end OModulePresheaf

end AlgebraicGeometry

end

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra

open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicCurve hiding genus cechDiff
open _root_.AlgebraicGeometry.RelPicard
open _root_.Opposite

namespace LiftA9

variable {X : Scheme.{u}}

theorem exists_hom_app_top_eq (N : X.Modules) (v : Γ(N, ⊤)) :
    ∃ s : 𝟙_ X.Modules ⟶ N, s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = v := by
  let sec : N.val.sections :=
    PresheafOfModules.sectionsMk (M := N.val) (fun U => N.presheaf.map (homOfLE (le_top : U.unop ≤
      ⊤)).op v)
      (by
        intro U V f
        change (N.presheaf ⋙ forget _).map f (N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op v) =
          N.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op v
        have hf : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
          Quiver.Hom.unop_inj (Subsingleton.elim _ _)
        rw [← hf, Functor.map_comp]
        rfl)
  refine ⟨N.unitHomEquiv.symm sec, ?_⟩
  have h1 := SheafOfModules.unitHomEquiv_apply_coe N (N.unitHomEquiv.symm sec) (op ⊤)
  rw [Equiv.apply_symm_apply] at h1
  have h2 : sec.val (op ⊤) = v := by
    change N.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op v = v
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Quiver.Hom.unop_inj
      (Subsingleton.elim _ _)
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  rw [← h2, h1]
  rfl

end LiftA9

namespace LCombA9

variable {X C : Scheme.{u}} (ε : X ⟶ C) {M : C.Modules}
  (e : (Scheme.Modules.pullback ε).obj M ≅ 𝟙_ X.Modules)

/-- Evaluation of a global module section after pullback and the specified trivialization. -/
noncomputable def cvalE (v : Γ(M, ⊤)) : Γ(X, ⊤) :=
  Scheme.Modules.ofUnitSection ⊤ (e.hom.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection ε v))

/-- Evaluation of a section morphism after pullback and the specified trivialization. -/
noncomputable def cval (s : 𝟙_ C.Modules ⟶ M) : Γ(X, ⊤) :=
  Scheme.Modules.ofUnitSection ⊤
    (e.hom.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection ε (s.app ⊤
      (Scheme.Modules.toUnitSection ⊤ 1))))

theorem cval_eq (s : 𝟙_ C.Modules ⟶ M) : cval ε e s = cvalE ε e (s.app ⊤
  (Scheme.Modules.toUnitSection ⊤ 1)) :=
  rfl

lemma cvalE_add (v v' : Γ(M, ⊤)) : cvalE ε e (v + v') = cvalE ε e v + cvalE ε e v' := by
  unfold cvalE
  rw [Scheme.Modules.pullbackLocalSection_add, map_add]
  rfl

lemma cvalE_zero : cvalE ε e (0 : Γ(M, ⊤)) = 0 := by
  unfold cvalE
  rw [Scheme.Modules.pullbackLocalSection_zero, map_zero]
  rfl

lemma cvalE_smul (g : Γ(C, ⊤)) (v : Γ(M, ⊤)) : cvalE ε e (g • v) = ε.appTop g * cvalE ε e v := by
  unfold cvalE
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul]
  rfl

lemma cvalE_sum {ι : Type*} (S : Finset ι) (v : ι → Γ(M, ⊤)) :
    cvalE ε e (∑ i ∈ S, v i) = ∑ i ∈ S, cvalE ε e (v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact cvalE_zero ε e
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cvalE_add, ih]

lemma app_pullbackSection_comp (s : 𝟙_ C.Modules ⟶ M) :
    (Scheme.Modules.pullbackSection ε s ≫ e.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      cval ε e s • Scheme.Modules.unitSection ⊤ := by
  rw [Scheme.Modules.smul_unitSection]
  change e.hom.app ⊤ (((Scheme.Modules.pullback ε).map s).app ⊤
    ((Scheme.Modules.pullbackUnitIso ε).inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) = _
  have h1 : (Scheme.Modules.pullbackUnitIso ε).inv.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (ε
    ⁻¹ᵁ ⊤) 1) =
      Scheme.Modules.pullbackLocalSection ε (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤))) := by
    have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection ε ⊤ (1 :
      Γ(C, ⊤))
    rw [map_one] at h
    rw [← h]
    change ((Scheme.Modules.pullbackUnitIso ε).hom ≫ (Scheme.Modules.pullbackUnitIso ε).inv).app _
      _ = _
    exact congrArg
      (fun φ : (Scheme.Modules.pullback ε).obj (𝟙_ C.Modules) ⟶
          (Scheme.Modules.pullback ε).obj (𝟙_ C.Modules) =>
        φ.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection ε
          (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤)))))
      (Scheme.Modules.pullbackUnitIso ε).hom_inv_id
  have h2 : ((Scheme.Modules.pullback ε).map s).app (ε ⁻¹ᵁ ⊤)
      (Scheme.Modules.pullbackLocalSection ε (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤)))) =
      Scheme.Modules.pullbackLocalSection ε (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :=
    (Scheme.Modules.pullbackLocalSection_app ε s _).symm
  change e.hom.app (ε ⁻¹ᵁ ⊤) (((Scheme.Modules.pullback ε).map s).app (ε ⁻¹ᵁ ⊤)
    ((Scheme.Modules.pullbackUnitIso ε).inv.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (ε ⁻¹ᵁ ⊤)
      1))) = _
  rw [h1, h2]
  rfl

lemma pullbackSection_app_top (s : 𝟙_ C.Modules ⟶ M) :
    (Scheme.Modules.pullbackSection ε s).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      (show Γ((Scheme.Modules.pullback ε).obj M, ⊤) from
        Scheme.Modules.pullbackLocalSection ε (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))) := by
  change ((Scheme.Modules.pullback ε).map s).app ⊤
    ((Scheme.Modules.pullbackUnitIso ε).inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) = _
  have h1 : (Scheme.Modules.pullbackUnitIso ε).inv.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (ε
    ⁻¹ᵁ ⊤) 1) =
      Scheme.Modules.pullbackLocalSection ε (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤))) := by
    have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection ε ⊤ (1 :
      Γ(C, ⊤))
    rw [map_one] at h
    rw [← h]
    change ((Scheme.Modules.pullbackUnitIso ε).hom ≫ (Scheme.Modules.pullbackUnitIso ε).inv).app _
      _ = _
    exact congrArg
      (fun φ : (Scheme.Modules.pullback ε).obj (𝟙_ C.Modules) ⟶
          (Scheme.Modules.pullback ε).obj (𝟙_ C.Modules) =>
        φ.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.pullbackLocalSection ε
          (Scheme.Modules.toUnitSection ⊤ (1 : Γ(C, ⊤)))))
      (Scheme.Modules.pullbackUnitIso ε).hom_inv_id
  change ((Scheme.Modules.pullback ε).map s).app (ε ⁻¹ᵁ ⊤)
    ((Scheme.Modules.pullbackUnitIso ε).inv.app (ε ⁻¹ᵁ ⊤) (Scheme.Modules.toUnitSection (ε ⁻¹ᵁ ⊤)
      1)) = _
  rw [h1]
  exact (Scheme.Modules.pullbackLocalSection_app ε s _).symm

lemma mem_support_iff (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ C.Modules ⟶ M) (p : X) :
    ε.base p ∈ (Scheme.Modules.zeroSchemeIdeal s).support ↔
      p ∈ (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection ε s ≫ e.hom)).support :=
        by
  rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso, ←
    Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal ε hM s,
    Scheme.IdealSheafData.support_comap]
  rfl

lemma mem_support_iff_mem_zeroLocus (hX : IsAffineOpen (⊤ : X.Opens)) (σ : 𝟙_ X.Modules ⟶ 𝟙_
  X.Modules)
    (cv : Γ(X, ⊤)) (hσ : σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = cv •
      Scheme.Modules.unitSection ⊤) (p : X) :
    p ∈ (Scheme.Modules.zeroSchemeIdeal σ).support ↔ p ∈ X.zeroLocus ({cv} : Set Γ(X, ⊤)) := by
  have hid := Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
    (Scheme.Modules.isInvertible_unit X) (Scheme.Modules.unitSection ⊤)
      (Scheme.Modules.isFrameOn_unitSection ⊤)
    σ cv hσ ⟨⊤, hX⟩ le_rfl
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, hX⟩) (Set.mem_univ p)]
  erw [hid]
  have hmap : X.presheaf.map (homOfLE (le_rfl : (⊤ : X.Opens) ≤ ⊤)).op cv = cv := by
    have : (homOfLE (le_rfl : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, X.presheaf.map_id]; rfl
  rw [hmap]
  change p ∈ X.zeroLocus (↑(Ideal.span {cv}) : Set Γ(X, ⊤)) ↔ _
  rw [Scheme.zeroLocus_span]

theorem mem_support_iff_cval_mem (hX : IsAffineOpen (⊤ : X.Opens)) (hM :
  Scheme.Modules.IsInvertible M)
    (s : 𝟙_ C.Modules ⟶ M) (p : X) :
    ε.base p ∈ (Scheme.Modules.zeroSchemeIdeal s).support ↔ cval ε e s ∈ (X.toSpecΓ.base p).asIdeal
      := by
  have hbo : ∀ (f : Γ(X, ⊤)) (q : X), q ∈ X.basicOpen f ↔ f ∉ (X.toSpecΓ.base q).asIdeal := by
    intro f q
    exact (congrArg (fun W : X.Opens => q ∈ W)
      (X.toSpecΓ_preimage_basicOpen f)).to_iff.symm
  rw [mem_support_iff ε e hM s p, mem_support_iff_mem_zeroLocus hX _ _ (app_pullbackSection_comp ε
    e s) p,
    Scheme.mem_zeroLocus_iff]
  simp only [Set.mem_singleton_iff, forall_eq, hbo, not_not]

end LCombA9

theorem _root_.AlgebraicGeometry.SmoothProperCurve.exists_section_invModule_pow_ker_disjoint
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule),
      ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
  classical
  let K : Type u := AlgebraicClosure (IsLocalRing.ResidueField R)
  let : Algebra R K := (algebraMap (IsLocalRing.ResidueField R) K).comp (algebraMap R _)
    |>.toAlgebra
  let ξ := Scheme.TwoAffineOpenCover.specMap R K
  let CK : Scheme.{u} := pullback c ξ
  let F : CK ⟶ C := pullback.fst c ξ
  let cK : CK ⟶ Spec (CommRingCat.of K) := pullback.snd c ξ
  let εK : SchemeHomOver (𝟙 _) cK := SmoothProperCurve.sectionBaseChange K ε
  have : IsProper cK := inferInstance
  have : SmoothOfRelativeDimension 1 cK := inferInstance
  have : GeometricallyIntegral cK := inferInstance
  have : IsIntegral CK := inferInstance
  have hker : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c) ε.1 ε.2
  have haff := AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset cK
  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top cK haff
  let 𝒱K : CK.TwoAffineOpenCover := ⟨U, V, hU, hV, hsup, hUV⟩
  obtain ⟨g, hg⟩ :=
    SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover K
      cK 𝒱K
  let gC : ℕ := Module.finrank K (𝒱K.sectionsOf cK (SheafOfModules.unit CK.ringCatSheaf :
    CK.Modules)).H1
  let m : ℕ := 2 * (g + gC) + 1
  let M : C.Modules := (ε.1.ker ^ m).invModule
  have hM : Scheme.Modules.IsInvertible M := (hker.pow m).isInvertible_invModule
  let 𝔪K : (Spec (CommRingCat.of K) : Scheme.{u}) := IsLocalRing.closedPoint K
  have h𝔪K : 𝔪K.asIdeal.IsMaximal := by
    change (IsLocalRing.maximalIdeal K).IsMaximal
    exact IsLocalRing.maximalIdeal.isMaximal K
  obtain ⟨sK, hsK⟩ :=
    SmoothProperCurve.exists_section_invModule_pow_ker_notMem_support_of_isMaximal K cK εK 𝒱K g hg m
      (by omega) (by omega) 𝔪K h𝔪K
  let S : Scheme.{u} := Spec (CommRingCat.of R)
  have hεc : ε.1 ≫ c = 𝟙 S := ε.2
  have : IsClosedImmersion (ε.1 ≫ c) := by rw [hεc]; infer_instance
  have : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 S)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback c (𝟙 S)) inferInstance
  have hσ1 : rigSection c (𝟙 S) ε ≫ pullback.snd c (𝟙 S) = 𝟙 S :=
    by simp only [rigSection, pullback.lift_snd]
  have hI1 : (rigSection c (𝟙 S) ε).ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (𝟙 S) ε) hσ1
  have hσ1π : rigSection c (𝟙 S) ε ≫ pullback.fst c (𝟙 S) = ε.1 := by
    simp only [rigSection, pullback.lift_fst, Category.id_comp]
  let ψ : SchemeHomOver ξ (𝟙 S) := ⟨ξ, Category.comp_id _⟩
  let g₁ : CK ⟶ pullback c (𝟙 S) := baseChangeSnd c ψ
  let π : pullback c (𝟙 S) ⟶ C := pullback.fst c (𝟙 S)
  have hg₁π : g₁ ≫ π = F := by
    simp only [g₁, π, F, baseChangeSnd, pullback.lift_fst, Category.comp_id]
  obtain ⟨eπ⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso π ε.1
    (rigSection c (𝟙 S) ε) hσ1π hker hI1 m).1
  obtain ⟨eψ⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ m
  have eK : (Scheme.Modules.pullback F).obj M ≅ (εK.1.ker ^ m).invModule :=
    (Scheme.Modules.pullbackCongr hg₁π.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp g₁ π).app
      _).symm ≪≫
      (Scheme.Modules.pullback g₁).mapIso eπ ≪≫ eψ
  have hM' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback F).obj M) := hM.pullback F
  have hkerK : εK.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := cK) εK.1
    εK.2
  let M₂ : CK.Modules := (εK.1.ker ^ m).invModule
  have hM₂ : Scheme.Modules.IsInvertible M₂ := (hkerK.pow m).isInvertible_invModule
  let M₁ : CK.Modules := (SheafOfModules.unit CK.ringCatSheaf : CK.Modules) ⊗ M₂
  have hM₁ : Scheme.Modules.IsInvertible M₁ := (Scheme.Modules.isInvertible_unit CK).tensor hM₂
  obtain ⟨hZfin, hZdeg, -, -⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := cK) εK.1 εK.2 m
  have hχ := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq cK
    (hkerK.pow m)
    hZfin hZdeg (SheafOfModules.unit CK.ringCatSheaf : CK.Modules)
      (Scheme.Modules.isInvertible_unit CK) 𝒱K
  have hH1two : Subsingleton (𝒱K.sectionsOf cK M₁).H1 := by
    apply Scheme.Modules.IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub K cK M₁ hM₁ 𝒱K
    have hm : (2 * (gC : ℤ) - 1) ≤ (m : ℤ) := by
      change (2 * (gC : ℤ) - 1) ≤ ((2 * (g + gC) + 1 : ℕ) : ℤ)
      push_cast
      omega
    change 2 * (gC : ℤ) - 1 ≤ _
    rw [hχ]
    linarith
  have hH1M₁ : Subsingleton ((OModulePresheaf.ofModules cK M₁).HSucc 𝒱K.toOrderedAffineCover 0) :=
    by
    have e := (OModulePresheaf.ofModules cK M₁).HSuccZeroEquiv 𝒱K
    exact (e.toEquiv.subsingleton_congr).mpr hH1two
  have e₁ : M₁ ≅ (Scheme.Modules.pullback F).obj M := (λ_ M₂) ≪≫ eK.symm
  have hH1F : Subsingleton ((OModulePresheaf.ofModules cK ((Scheme.Modules.pullback F).obj M)).HSucc
      𝒱K.toOrderedAffineCover 0) := by
    obtain ⟨e⟩ := (OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso cK e₁
      𝒱K.toOrderedAffineCover).2.1 0
    exact (e.toEquiv.subsingleton_congr).mp hH1M₁
  have hH1 : ∀ 𝒲 : CK.OrderedAffineCover,
      Subsingleton ((OModulePresheaf.ofModules cK ((Scheme.Modules.pullback F).obj M)).HSucc 𝒲 0)
        := fun 𝒲 =>
    OModulePresheaf.subsingleton_HSucc_zero_ofModules_of_subsingleton cK _ hM'.exists_trivialization
      𝒱K.toOrderedAffineCover 𝒲 hH1F
  have hfin : ∀ 𝒰 : C.OrderedAffineCover, (OModulePresheaf.ofModules c M).CechFinite 𝒰 := fun 𝒰 =>
    OModulePresheaf.cechFinite_ofModules_of_locallyTrivial c M hM.exists_trivialization 𝒰
  let τ : Fin 1 → Γ((Scheme.Modules.pullback F).obj M, ⊤) :=
    fun _ => (sK ≫ eK.inv).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
  obtain ⟨N, mj, cj, hτ⟩ :=
    Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc R c M hM hfin K hH1 τ
  have hPicK : ∀ (N : Type u) [AddCommGroup N] [Module K N], Module.Invertible K N → Module.Free K
    N :=
    CommRing.Pic.subsingleton_iff.mp inferInstance
  obtain ⟨eX⟩ := Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free K hPicK _
    (hM'.pullback εK.1)
  have hXaff : IsAffineOpen (⊤ : (Spec (CommRingCat.of K)).Opens) := isAffineOpen_top _
  have hsj : ∀ j, ∃ sj : 𝟙_ C.Modules ⟶ M, sj.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = mj j :=
    fun j => LiftA9.exists_hom_app_top_eq M (mj j)
  choose sj hsj using hsj
  let 𝔭 : Ideal Γ(Spec (CommRingCat.of K), ⊤) := ((Spec (CommRingCat.of K)).toSpecΓ.base 𝔪K).asIdeal
  have ht' : LCombA9.cval εK.1 eX (sK ≫ eK.inv) ∉ 𝔭 := by
    intro hmem
    apply hsK
    rw [← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso sK eK.inv,
      LCombA9.mem_support_iff_cval_mem εK.1 eX hXaff hM' (sK ≫ eK.inv) 𝔪K]
    exact hmem
  have hexp : LCombA9.cval εK.1 eX (sK ≫ eK.inv) =
      ∑ j, εK.1.appTop (cK.appTop ((Scheme.ΓSpecIso (.of K)).inv (cj 0 j))) *
        LCombA9.cval εK.1 eX (Scheme.Modules.pullbackSection F (sj j)) := by
    rw [LCombA9.cval_eq]
    have h0 : (sK ≫ eK.inv).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = τ 0 := rfl
    rw [h0, hτ 0, LCombA9.cvalE_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LCombA9.cvalE_smul, LCombA9.cval_eq, LCombA9.pullbackSection_app_top, hsj j]
    rfl
  have hj : ∃ j, LCombA9.cval εK.1 eX (Scheme.Modules.pullbackSection F (sj j)) ∉ 𝔭 := by
    by_contra hall
    push Not at hall
    apply ht'
    rw [hexp]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hall j)
  obtain ⟨j, hj⟩ := hj
  have hjK : εK.1.base 𝔪K ∉ (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F (sj
    j))).support := by
    rw [LCombA9.mem_support_iff_cval_mem εK.1 eX hXaff hM' _ 𝔪K]
    exact hj
  have hjC : F.base (εK.1.base 𝔪K) ∉ (Scheme.Modules.zeroSchemeIdeal (sj j)).support := by
    intro hmem
    apply hjK
    rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal F hM (sj j),
      Scheme.IdealSheafData.support_comap]
    exact hmem
  have hFε : F.base (εK.1.base 𝔪K) = ε.1.base (ξ.base 𝔪K) := by
    change (εK.1 ≫ F).base 𝔪K = (ξ ≫ ε.1).base 𝔪K
    rw [SmoothProperCurve.sectionBaseChange_coe_fst]
  rw [hFε] at hjC
  have hξ : ξ.base 𝔪K = IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    change ((Scheme.TwoAffineOpenCover.specMap R K).base (IsLocalRing.closedPoint K)).asIdeal =
      (IsLocalRing.closedPoint R).asIdeal
    rw [Scheme.TwoAffineOpenCover.specMap]
    change (PrimeSpectrum.comap (algebraMap R K) (IsLocalRing.closedPoint K)).asIdeal =
      (IsLocalRing.closedPoint R).asIdeal
    rw [PrimeSpectrum.comap_asIdeal]
    change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = IsLocalRing.maximalIdeal R
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField K), ← RingHom.ker_eq_comap_bot]
    change RingHom.ker ((algebraMap (IsLocalRing.ResidueField R) K).comp (algebraMap R
      (IsLocalRing.ResidueField R))) = _
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp
      ((algebraMap (IsLocalRing.ResidueField R) K).injective), ← RingHom.ker_eq_comap_bot,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have h7 : ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal (sj j)).support := by
    rintro x ⟨p, rfl⟩ hp
    apply hjC
    rw [hξ]
    have hspec : ε.1.base p ⤳ ε.1.base (IsLocalRing.closedPoint R) :=
      (IsLocalRing.specializes_closedPoint p).map ε.1.base.hom.continuous
    exact hspec.mem_closed (Scheme.Modules.zeroSchemeIdeal (sj j)).support.isClosed hp
  exact ⟨m, by omega, sj j, h7⟩
end SmoothProperCurve_exists_section_invModule_pow_ker_disjoint
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
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
  ProjSpaceCech.Idx.instDecidableEq
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
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
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
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
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
attribute [-simp] AlgebraicGeometry.OModulePresheaf.im_obj
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
  ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
attribute [-simp] AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.Divisor.mapRestrict_single
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
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
attribute [-simp] AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul

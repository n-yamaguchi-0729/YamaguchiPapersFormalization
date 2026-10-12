/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import Nyll.AlgebraicCurves.Geometry.Deformation.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
import Nyll.JacobianVarieties.Picard.CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
The genus determines the relative dimension of the representing Picard scheme.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PicardGenusDimension
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
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
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsLocallyInjectiveFunUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.RelPicard.isOpenImmersion_toGlued
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
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
  PresheafOfModules.ExteriorPower.instModulePresheafAb
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsFiltered
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
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
attribute [-instance]
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
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance]
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.SquareZero.isLocalRing'
  AlgebraicGeometry.SquareZero.isLocalRing
attribute [-simp]
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  CategoryTheory.Functor.OverTotal.ofFibre_fst
  CategoryTheory.Functor.overTotal_map_fst
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t'
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-simp]
  uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc
attribute [-simp]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U
attribute [-simp]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
  AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one
  AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
  AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
  AlgebraicGeometry.mapOnProdOver_fst
attribute [-simp]
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.fst_toProdSpec
  AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc
  AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
attribute [-simp]
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq
  AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply
  AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule
  AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
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
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
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
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
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
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp
  AlgebraicGeometry.RelEffCartierDiv.functor_map_fst
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ
  AlgebraicGeometry.TangentPoints.map_coe
  AlgebraicGeometry.SquareZero.basePoint_toBase_assoc
  AlgebraicGeometry.SquareZero.basePoint_toBase
  AlgebraicGeometry.SquareZero.basePoint_specMap
  AlgebraicGeometry.SquareZero.basePointOver_coe
  AlgebraicGeometry.SquareZero.specMap_toBase_assoc
  AlgebraicGeometry.SquareZero.specMapOver_coe
  AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe
  AlgebraicGeometry.SquareZero.specMap_toBase
  AlgebraicGeometry.SquareZero.basePoint_specMap_assoc

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian AlgebraicCurve

universe u v

namespace P2mJacDim

section Compare

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε}
  {D D' : RelativePic0Designation R c}

/-- The comparison morphism supplied by the two representing properties. -/
def compare (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c ε P D') :
    SchemeHomOver D.toBase D'.toBase :=
  h'.classify D.toBase h.poincare h.poincare_mem

theorem compare_comp_compare (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c ε P D') :
    (compare h h').1 ≫ (compare h' h).1 = 𝟙 D.P := by
  have key : postComp (compare h' h) (compare h h') = (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver
    D.toBase D.toBase) := by
    apply h.ext_of_iso D.toBase
    have e1 : (h.poincare.pullbackAlong (postComp (compare h' h) (compare h h'))).L ≅
        ((h.poincare.pullbackAlong (compare h' h)).pullbackAlong (compare h h')).L :=
      (RigidifiedLineBundle.pullbackAlongPullbackAlongIso h.poincare (compare h' h) (compare h
        h')).symm
    have e2 : Nonempty (((h.poincare.pullbackAlong (compare h' h)).pullbackAlong (compare h h')).L ≅
        (h'.poincare.pullbackAlong (compare h h')).L) :=
      RigidifiedLineBundle.pullbackAlong_congr (compare h h')
        (h.classify_spec D'.toBase h'.poincare h'.poincare_mem)
    have e3 : Nonempty ((h'.poincare.pullbackAlong (compare h h')).L ≅ h.poincare.L) :=
      h'.classify_spec D.toBase h.poincare h.poincare_mem
    have e4 : h.poincare.L ≅ (h.poincare.pullbackAlong (⟨𝟙 D.P, Category.id_comp _⟩ : SchemeHomOver
      D.toBase D.toBase)).L :=
      (RigidifiedLineBundle.pullbackAlongIdIso h.poincare).symm
    exact ⟨e1 ≪≫ e2.some ≪≫ e3.some ≪≫ e4⟩
  exact congrArg Subtype.val key

theorem isIso_compare (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c ε P D') :
    IsIso (compare h h').1 :=
  ⟨(compare h' h).1, compare_comp_compare h h', compare_comp_compare h' h⟩

end Compare

theorem irreducibleSpace_of_connectedSpace (K : Type u) [Field K] [IsAlgClosed K] {G : Scheme.{u}}
    {f : G ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f] [QuasiCompact f] (L :
      RelativeGroupLaw K f)
    [ConnectedSpace G] : IrreducibleSpace G := by
  obtain ⟨G₀, i, -, hio, -, hirr, hrange, -⟩ :=
    RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      K L
  have hsurj : Set.range i = Set.univ := by
    rw [hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  have : Epi i.base := (TopCat.epi_iff_surjective _).mpr (Set.range_eq_univ.mp hsurj)
  have : IsIso i := IsOpenImmersion.isIso i
  exact i.homeomorph.irreducibleSpace_iff.mp hirr

theorem main (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D) :
    SmoothOfRelativeDimension (genusFF K F) D.toBase := by
  obtain ⟨D₀, ⟨h₀⟩, hsm₀, hpr₀, hgc₀⟩ :=
    AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed K
      M.toBase s
  have : IsIso (compare h h₀).1 := isIso_compare h h₀
  have hfac : D.toBase = (compare h h₀).1 ≫ D₀.toBase := (compare h h₀).2.symm
  have : Smooth D.toBase := by rw [hfac]; infer_instance
  have : IsProper D.toBase := by rw [hfac]; infer_instance
  have : ConnectedSpace D₀.P :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D₀.toBase)
  have : ConnectedSpace D.P := (compare h h₀).1.homeomorph.connectedSpace_iff.mpr inferInstance
  have : IrreducibleSpace D.P :=
    irreducibleSpace_of_connectedSpace K
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h)
  exact AlgebraicGeometry.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq D.toBase
    D.zeroSection
    D.zeroSection_toBase (genusFF K F)
    (AlgebraicCurve.CurveModel.finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic
      K F hfg M s D h)

end P2mJacDim

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian AlgebraicCurve

universe u v
end JacobianVarieties.Picard.Proofs.PicardGenusDimension

namespace AlgebraicCurve.CurveModel

open _root_.JacobianVarieties.Picard.Proofs.PicardGenusDimension
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.RelPicard
  _root_.NeronModelInfra _root_.GoodReductionJacobian _root_.AlgebraicCurve
universe u v


/-- The representing Picard scheme is smooth of relative dimension equal to the genus. -/
theorem smoothOfRelativeDimension_genusFF_of_representsRelSubPic
    (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D) :
    SmoothOfRelativeDimension (genusFF K F) D.toBase :=
  P2mJacDim.main K F hfg M s D h
end AlgebraicCurve.CurveModel
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  PresheafOfModules.instMonoidalClosed
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
attribute [-instance]
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
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
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsLocallyInjectiveFunUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.RelPicard.isOpenImmersion_toGlued
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
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
  PresheafOfModules.ExteriorPower.instModulePresheafAb
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
attribute [-instance]
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
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
attribute [-instance]
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
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
attribute [-instance]
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.SquareZero.isLocalRing'
  AlgebraicGeometry.SquareZero.isLocalRing
attribute [-simp]
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.mulAdele_apply
attribute [-simp]
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  CategoryTheory.Functor.OverTotal.ofFibre_fst
  CategoryTheory.Functor.overTotal_map_fst
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t'
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-simp]
  uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc
attribute [-simp]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
  AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
attribute [-simp]
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.fst_toProdSpec
  AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc
  AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq
  AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply
  AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule
  AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
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
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
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
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
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
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp
attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.functor_map_fst
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ
  AlgebraicGeometry.TangentPoints.map_coe
  AlgebraicGeometry.SquareZero.basePoint_toBase_assoc
  AlgebraicGeometry.SquareZero.basePoint_toBase
  AlgebraicGeometry.SquareZero.basePoint_specMap
  AlgebraicGeometry.SquareZero.basePointOver_coe
  AlgebraicGeometry.SquareZero.specMap_toBase_assoc
  AlgebraicGeometry.SquareZero.specMapOver_coe
  AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe
  AlgebraicGeometry.SquareZero.specMap_toBase
  AlgebraicGeometry.SquareZero.basePoint_specMap_assoc

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafEulerChar
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.JacobianVarieties.Picard.AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_topologicalKrullDim_le
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_le_topologicalKrullDim
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_isIntegral_of_field
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.SchemeTheory.Modules.ProjectivePresentationBaseChange
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_FiniteBySections_tensor

/-!
# A symmetric line bundle with positive Euler coefficient

This file constructs an invertible sheaf on an abelian scheme that is isomorphic to its pullback
by group inversion. Its tensor powers have polynomial Euler characteristic with a positive
coefficient in the relative dimension.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SymmetricEulerCoefficient
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
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
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
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
attribute [-instance]
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
attribute [-instance]
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
attribute [-instance]
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
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
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued
  AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀
  AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase
  AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase
  AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀
  AlgebraicCurve.CurveModel.isOpenImmersion_fInf
attribute [-instance]
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase
  AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing
  AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing
  AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing
  AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
  instTopologicallyFGOfFiniteType
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-simp]
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
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
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
attribute [-simp]
  AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul
  AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
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
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
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
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
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
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
attribute [-simp]
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
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
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
attribute [-simp]
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
attribute [-simp]
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
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
  AlgebraicCurve.CurveModel.coe_gInf
  AlgebraicCurve.CurveModel.coe_tInvChart
  AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc
  AlgebraicCurve.CurveModel.ιInf_gluedToBase
  AlgebraicCurve.CurveModel.primeOfι₀_asIdeal
  AlgebraicCurve.CurveModel.coe_tChart
  AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc
  AlgebraicCurve.CurveModel.primeOfιInf_asIdeal
  AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_tma
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces
attribute [-simp]
  AlgebraicGeometry.ProjSpace.twistObj.mk.injEq
  AlgebraicGeometry.ProjSpace.twistObj.zero_val
  AlgebraicGeometry.ProjSpace.twistObj.add_val
  AlgebraicGeometry.ProjSpace.twist_res_val
  AlgebraicGeometry.ProjSpace.twist_smul_val
  AlgebraicGeometry.ProjSpace.twistGradeToObj_val
  AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace P2mSymAmpleTop

section Inv

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  let _ : Group (SchemeHomOver t' f) := G.pointGroup t'
  have h : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x)) *
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = 1 at h
  exact eq_inv_of_mul_eq_one_left h

theorem inv_inv_apply {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.inv t (G.inv t x) = x := by
  let _ : Group (SchemeHomOver t f) := G.pointGroup t
  exact inv_inv x

/-- The scheme morphism underlying inversion in the relative group law. -/
abbrev invMor : A ⟶ A := (G.inv f RelativeGroupLaw.idPoint).1

theorem invMor_over : invMor G ≫ f = f := (G.inv f RelativeGroupLaw.idPoint).2

theorem invMor_comp_invMor : invMor G ≫ invMor G = 𝟙 A := by
  have h1 : (GoodReductionJacobian.schemeHomOverComp (invMor G) (invMor_over G)
      (G.inv f RelativeGroupLaw.idPoint)).1 = invMor G ≫ invMor G := rfl
  have h2 : GoodReductionJacobian.schemeHomOverComp (invMor G) (invMor_over G)
      (RelativeGroupLaw.idPoint : SchemeHomOver f f) = G.inv f RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    change invMor G ≫ 𝟙 A = invMor G
    exact Category.comp_id _
  rw [← h1, inv_natural, h2, inv_inv_apply]

scoped instance isIso_invMor : IsIso (invMor G) :=
  ⟨⟨invMor G, invMor_comp_invMor G, invMor_comp_invMor G⟩⟩

end Inv

section Square

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (G : RelativeGroupLaw K f)

theorem isPullback_invMor :
    IsPullback (invMor G) f f (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Spec.map_id _
  rw [hid]
  exact IsPullback.of_horiz_isIso ⟨by rw [invMor_over, Category.comp_id]⟩

end Square

section Skel

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem cls_tensor (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  Skeleton.toSkeleton_tensorObj X Y

omit [MonoidalCategory C] in
theorem cls_congr {X Y : C} (e : X ≅ Y) : toSkeleton X = toSkeleton Y :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩

end Skel

section Symm

variable {A : Scheme.{u}} (e : A ⟶ A) (he : e ≫ e = 𝟙 A)

theorem cls_pullback_tensor (X Y : A.Modules) :
    toSkeleton ((Scheme.Modules.pullback e).obj (X ⊗ Y)) =
      toSkeleton ((Scheme.Modules.pullback e).obj X) * toSkeleton ((Scheme.Modules.pullback e).obj
        Y) := by
  rw [cls_congr (Scheme.Modules.pullbackTensorObjIso e X Y), cls_tensor]

include he in
theorem nonempty_pullback_pullback_iso (X : A.Modules) :
    Nonempty ((Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback e).obj X) ≅ X) :=
  ⟨(Scheme.Modules.pullbackComp e e).app X ≪≫ (Scheme.Modules.pullbackCongr he).app X ≪≫
    (Scheme.Modules.pullbackId A).app X⟩

include he in
theorem nonempty_pullback_symm_iso (𝓛₀ : A.Modules) :
    Nonempty ((Scheme.Modules.pullback e).obj (𝓛₀ ⊗ (Scheme.Modules.pullback e).obj 𝓛₀) ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback e).obj 𝓛₀) := by
  obtain ⟨i⟩ := nonempty_pullback_pullback_iso e he 𝓛₀
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [cls_pullback_tensor, cls_congr i, cls_tensor, mul_comm]

end Symm

theorem main
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f) (g : ℕ)
      [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback (L.inv f RelativeGroupLaw.idPoint).1).obj 𝓛 ≅ 𝓛) ∧
      ∃ q : Polynomial ℚ, 0 < q.coeff g ∧
        ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ)
          := by
  have : IsIntegral A := hA.isIntegral_of_field
  have hdim : topologicalKrullDim A = g :=
    le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f g)
      (SmoothOfRelativeDimension.le_topologicalKrullDim f g)
  obtain ⟨𝓛₀, h𝓛₀, N, 𝔓, hfin⟩ := AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections
    K f hA
  obtain ⟨𝔓', -, -, hsq⟩ :=
    Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (isPullback_invMor L) 𝔓
  have hfin' : IsFinite 𝔓'.toProj :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin
  have hfs' : ((Scheme.Modules.pullback (invMor L)).obj 𝓛₀).FiniteBySections f := ⟨N, 𝔓', hfin'⟩
  refine ⟨𝓛₀ ⊗ (Scheme.Modules.pullback (invMor L)).obj 𝓛₀,
    h𝓛₀.tensor (h𝓛₀.pullback (invMor L)), nonempty_pullback_symm_iso (invMor L) (invMor_comp_invMor
      L) 𝓛₀, ?_⟩
  exact Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq f
    g hdim _
    (h𝓛₀.tensor (h𝓛₀.pullback (invMor L))) (Scheme.Modules.FiniteBySections.tensor ⟨N, 𝔓, hfin⟩
      hfs') 𝒦

end P2mSymAmpleTop
end JacobianVarieties.Picard.Proofs.SymmetricEulerCoefficient

namespace GoodReductionJacobian.RelativeGroupLaw

open _root_.JacobianVarieties.Picard.Proofs.SymmetricEulerCoefficient
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra
universe u


/-- A symmetric invertible sheaf has positive Euler coefficient in the relative dimension. -/
theorem exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f) (g : ℕ)
      [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback (L.inv f RelativeGroupLaw.idPoint).1).obj 𝓛 ≅ 𝓛) ∧
      ∃ q : Polynomial ℚ, 0 < q.coeff g ∧
        ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) :=
  P2mSymAmpleTop.main K f L hA g 𝒦
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation

attribute [-instance]
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
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
attribute [-instance]
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
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
attribute [-instance]
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
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
attribute [-instance]
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
  AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued
  AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀
  AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase
  AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase
  AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀
  AlgebraicCurve.CurveModel.isOpenImmersion_fInf
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase
  AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing
  AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing
  AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing
  AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
attribute [-instance]
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
  instTopologicallyFGOfFiniteType
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
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
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul
  AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
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
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  CategoryTheory.Functor.OverTotal.ofFibre_fst
  CategoryTheory.Functor.overTotal_map_fst
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf
attribute [-simp]
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
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
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
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
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
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
attribute [-simp]
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
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
attribute [-simp]
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
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
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
  AlgebraicCurve.CurveModel.coe_gInf
  AlgebraicCurve.CurveModel.coe_tInvChart
  AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc
attribute [-simp]
  AlgebraicCurve.CurveModel.ιInf_gluedToBase
  AlgebraicCurve.CurveModel.primeOfι₀_asIdeal
  AlgebraicCurve.CurveModel.coe_tChart
  AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc
  AlgebraicCurve.CurveModel.primeOfιInf_asIdeal
  AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_tma
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces
  AlgebraicGeometry.ProjSpace.twistObj.mk.injEq
  AlgebraicGeometry.ProjSpace.twistObj.zero_val
  AlgebraicGeometry.ProjSpace.twistObj.add_val
  AlgebraicGeometry.ProjSpace.twist_res_val
  AlgebraicGeometry.ProjSpace.twist_smul_val
  AlgebraicGeometry.ProjSpace.twistGradeToObj_val
  AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

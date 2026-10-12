/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_abelJacobi_of_curveModel.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Models.CurveModel_exists_divisorClassMap
import Nyll.AlgebraicCurves.Divisors.Exists_list_isPrincipal_sub_sum_single_sub_smul_single
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Nyll.JacobianVarieties.Picard.IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Nyll.AlgebraicCurves.Geometry.Picard.IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_sup_eq_top
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Picard classes and points for a curve model

Identify degree-zero divisor classes with represented Picard points and compare Abel-Jacobi
maps.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.Exists_pic0_equiv_points_abelJacobi_of_curveModel
attribute [-instance]
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
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
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
attribute [-instance]
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
attribute [-simp]
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
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.degree_pushforwardAlong
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
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
  AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq
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
attribute [-simp]
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
  AlgebraicGeometry.ChowDatum.mk.injEq
attribute [-simp]
  ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc

universe u v

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.GoodReductionJacobian
open _root_.AlgebraicCurve

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace PtsCoreGlue
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

theorem twoAffineOpenCover_ext {Y : Scheme.{u}} {𝒲 𝒲' : Y.TwoAffineOpenCover}
    (h0 : 𝒲.U0 = 𝒲'.U0) (h1 : 𝒲.U1 = 𝒲'.U1) : 𝒲 = 𝒲' := by
  obtain ⟨U0, U1, _, _, _, _⟩ := 𝒲
  obtain ⟨U0', U1', _, _, _, _⟩ := 𝒲'
  dsimp only at h0 h1
  subst h0
  subst h1
  rfl

theorem preimage_id_opens {Y : Scheme.{u}} (U : Y.Opens) : (𝟙 Y) ⁻¹ᵁ U = U := rfl


theorem nonempty_linearEquiv_of_iso {k : Type u} [Field k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    Nonempty ((𝒲.sectionsOf y M).H0 ≃ₗ[k] (𝒲.sectionsOf y M').H0) ∧
      Nonempty ((𝒲.sectionsOf y M).H1 ≃ₗ[k] (𝒲.sectionsOf y M').H1) := by
  obtain ⟨𝒲', h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y)
      (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  have h𝒲 : 𝒲' = 𝒲 :=
    twoAffineOpenCover_ext (h0.trans (preimage_id_opens _)) (h1.trans (preimage_id_opens _))
  subst h𝒲
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem eulerChar_congr {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    (𝒲 : Y.TwoAffineOpenCover) {M M' : Y.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1
      = (Module.finrank k (𝒲.sectionsOf y M').H0 : ℤ)
          - Module.finrank k (𝒲.sectionsOf y M').H1 := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso y 𝒲 e
  rw [e0.finrank_eq, e1.finrank_eq]


/-- Identify successive pullbacks with pullback along the specified composite map. -/
def pullbackCompCompIso {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ Z) (q : Z ⟶ W) (g : X ⟶ W)
    (hfac : (f ≫ s) ≫ q = g) (L : W.Modules) :
    (Scheme.Modules.pullback (f ≫ s)).obj ((Scheme.Modules.pullback q).obj L)
        ≅ (Scheme.Modules.pullback g).obj L :=
  (Scheme.Modules.pullbackComp (f ≫ s) q).app L ≪≫ (Scheme.Modules.pullbackCongr hfac).app L


/-- Identify a module with its pullback along an isomorphism followed by its inverse. -/
def isoPullbackInvPullbackObj {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIso p] (L : Y.Modules) :
    L ≅ (Scheme.Modules.pullback (inv p)).obj ((Scheme.Modules.pullback p).obj L) :=
  ((Scheme.Modules.pullbackComp (inv p) p ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id p) ≪≫
      Scheme.Modules.pullbackId Y).app L).symm

end AlgebraicGeometry.RelPicard.PtsCoreGlue

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace PtsCoreGlue
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


/-- The compatible family of local sections obtained by restricting a global section. -/
noncomputable def sectionsOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤))
    : SheafOfModules.sections L :=
  PresheafOfModules.sectionsMk (M := L.val)
    (fun U => (L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m : Γ(L, U.unop)))
    (by
      intro U V f
      change (L.presheaf.map f) ((L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) m) =
        (L.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) m
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun g => (L.presheaf.map g) m) (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

theorem sectionsOfGlobal_top {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (sectionsOfGlobal L m).1 (Opposite.op ⊤) = m := by
  change (L.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) m = m
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _
    := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]
  rfl


/-- The morphism from the unit module determined by a global section. -/
noncomputable def homOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : 𝟙_ X.Modules ⟶ L :=
  (SheafOfModules.unitHomEquiv L).symm (sectionsOfGlobal L m)

theorem app_homOfGlobal_one {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (Scheme.Modules.Hom.app (homOfGlobal L m) ⊤) (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  have h1 := SheafOfModules.unitHomEquiv_apply_coe L (homOfGlobal L m) (Opposite.op ⊤)
  rw [homOfGlobal, Equiv.apply_symm_apply, sectionsOfGlobal_top] at h1
  exact h1.symm

theorem homOfGlobal_ne_zero {X : Scheme.{u}} (L : X.Modules) {m : Γ(L, ⊤)} (hm : m ≠ 0) :
    homOfGlobal L m ≠ 0 := by
  intro h0
  apply hm
  have h1 := app_homOfGlobal_one L m
  rw [h0, Scheme.Modules.Hom.zero_app] at h1
  exact h1.symm.trans (AddCommGrpCat.zero_apply _ _ _)


theorem exists_hom_ne_zero_of_nontrivial_H0 {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) (L : X.Modules) (hL : Nontrivial (𝒱.sectionsOf x L).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ L, s ≠ 0 := by
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x L
  have : Nontrivial Γ(L, ⊤) := e.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(L, ⊤))
  exact ⟨homOfGlobal L m, homOfGlobal_ne_zero L hm⟩


theorem nontrivial_H0_tensorUnit {k : Type u} [Field k] {X : Scheme.{u}} [Nonempty X]
    (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) : Nontrivial (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 := by
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x (𝟙_ X.Modules)
  obtain ⟨pt⟩ := ‹Nonempty X›
  have : Nontrivial Γ(X, ⊤) := (X.presheaf.germ ⊤ pt trivial).hom.domain_nontrivial
  have : Nontrivial Γ((𝟙_ X.Modules : X.Modules), ⊤) :=
    Function.Injective.nontrivial (f := Scheme.Modules.toUnitSection (X := X) ⊤)
      (fun a b h => by
        have h' := congrArg (Scheme.Modules.ofUnitSection (X := X) ⊤) h
        rw [Scheme.Modules.ofUnitSection_toUnitSection,
          Scheme.Modules.ofUnitSection_toUnitSection] at h'
        exact h')
  exact e.symm.toEquiv.nontrivial


theorem nonempty_twoAffineOpenCover_of_iso {X X' : Scheme.{u}} (φ : X ≅ X')
    (𝒱' : X'.TwoAffineOpenCover) :
    Nonempty X.TwoAffineOpenCover := by
  obtain ⟨𝒱, -, -, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (R := Γ(X', ⊤)) (φ.hom ≫ X'.toSpecΓ) X'.toSpecΓ φ rfl 𝒱' (𝟙_ X'.Modules)
    ((Scheme.Modules.pullback φ.hom).obj (𝟙_ X'.Modules)) (Iso.refl _)
  exact ⟨𝒱⟩

end AlgebraicGeometry.RelPicard.PtsCoreGlue

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace PtsCoreGlue
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


theorem isIso_toProdSpec {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    IsIso (toProdSpec a) :=
  ⟨⟨pullback.fst a (𝟙 _), toProdSpec_fst a, fst_toProdSpec a⟩⟩

theorem toProdSpec_snd {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    toProdSpec a ≫ pullback.snd a (𝟙 _) = a :=
  pullback.lift_snd _ _ _


theorem comp_toProdSpec_eq_graphOver {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ C) (hf : f ≫ c = y)
    (q : Spec (CommRingCat.of k) ⟶ Y) (hq : q ≫ y = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ C)
    (ht : t ≫ c = 𝟙 _) (hqt : q ≫ f = t) :
    q ≫ (f ≫ toProdSpec c) = graphOver c t ht := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, toProdSpec_fst, Category.comp_id, graphOver_fst, hqt]
  · rw [Category.assoc, Category.assoc, toProdSpec_snd, graphOver_snd, hf, hq]


theorem nonempty_pullback_lineBundle_ofPoint_iso {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (q : Spec (CommRingCat.of k) ⟶ Y) (hq : q ≫ y = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ C)
    (ht : t ≫ c = 𝟙 _) (hqt : q ≫ f = t) :
    Nonempty ((Scheme.Modules.pullback (f ≫ toProdSpec c)).obj
        (RelEffCartierDiv.ofPoint c t ht).lineBundle ≅
      ((q.ker) ^ 1).invModule) := by
  have := isIso_toProdSpec c
  have hI : (graphOver c t ht).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c t ht)
  have hI' : q.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := y) q hq
  obtain ⟨e⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (f ≫ toProdSpec c)
    (graphOver c t ht) q (comp_toProdSpec_eq_graphOver c y f hf q hq t ht hqt) hI hI' 1).1
  exact ⟨(Scheme.Modules.pullback (f ≫ toProdSpec c)).mapIso
      (eqToIso (congrArg Scheme.IdealSheafData.invModule
          (pow_one (graphOver c t ht).ker))).symm ≪≫ e⟩


theorem nonempty_pullback_idealModule_ofPoint_iso {k : Type u} [Field k] {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (q : Spec (CommRingCat.of k) ⟶ Y) (hq : q ≫ y = 𝟙 _) (t : Spec (CommRingCat.of k) ⟶ C)
    (ht : t ≫ c = 𝟙 _) (hqt : q ≫ f = t) :
    Nonempty ((Scheme.Modules.pullback (f ≫ toProdSpec c)).obj
        (RelEffCartierDiv.ofPoint c t ht).idealModule ≅
      ((q.ker) ^ 1).module) := by
  have := isIso_toProdSpec c
  have hI : (graphOver c t ht).ker.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c t ht)
  have hI' : q.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := y) q hq
  obtain ⟨e⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso (f ≫ toProdSpec c)
    (graphOver c t ht) q (comp_toProdSpec_eq_graphOver c y f hf q hq t ht hqt) hI hI' 1).2
  exact ⟨(Scheme.Modules.pullback (f ≫ toProdSpec c)).mapIso
      (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one (graphOver c t ht).ker))).symm ≪≫ e⟩


theorem nonempty_pullback_pointsSubBasepointModule_iso_foldr
    {k : Type u} [Field k] {C Y : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f] (hf : f ≫ c = y)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) (hε : ε'.1 ≫ f = ε.1)
    (Ps : List {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) :
    Nonempty ((Scheme.Modules.pullback (f ≫ toProdSpec c)).obj
        (pointsSubBasepointModule (a := c) ε
          (Ps.map fun P => (⟨P.1 ≫ f, by rw [Category.assoc, hf, P.2]⟩
              : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))) ≅
      Ps.foldr (fun P A => ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) ⊗ A)
        (𝟙_ Y.Modules)) := by
  induction Ps with
  | nil =>
      simp only [List.map_nil, List.foldr_nil, pointsSubBasepointModule_nil]
      exact ⟨Scheme.Modules.pullbackTensorUnitObjIso (f ≫ toProdSpec c)⟩
  | cons P Ps ih =>
      obtain ⟨eT⟩ := ih
      obtain ⟨eP⟩ := nonempty_pullback_lineBundle_ofPoint_iso c y f hf P.1 P.2 (P.1 ≫ f)
        (by rw [Category.assoc, hf, P.2]) rfl
      obtain ⟨eE⟩ := nonempty_pullback_idealModule_ofPoint_iso c y f hf ε'.1 ε'.2 ε.1 ε.2 hε
      simp only [List.map_cons, List.foldr_cons, pointsSubBasepointModule_cons]
      exact ⟨Scheme.Modules.pullbackTensorObjIso (f ≫ toProdSpec c) _ _ ≪≫
        tensorIso (Scheme.Modules.pullbackTensorObjIso (f ≫ toProdSpec c) _ _ ≪≫ tensorIso eP eE)
          eT⟩


theorem isClosedImmersion_of_comp_eq_id {X S : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] (σ : S ⟶ X)
    (hσ : σ ≫ p = 𝟙 S) : IsClosedImmersion σ := by
  have : IsClosedImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  exact .of_comp σ p


theorem comp_lift_eq_comp_toProdSpec_baseChangeSnd {k : Type u} [Field k] {C Y T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) (f : Y ⟶ C)
    (t : T ⟶ Spec (CommRingCat.of k)) (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (h : 𝟙 C ≫ c = (c ≫ x) ≫ t) :
    f ≫ pullback.lift (𝟙 C) (c ≫ x) h =
      (f ≫ toProdSpec c) ≫ baseChangeSnd c
        (⟨x, hx⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, baseChangeSnd,
      pullback.lift_fst, toProdSpec_fst_assoc, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, baseChangeSnd,
      pullback.lift_snd, ← Category.assoc (toProdSpec c), toProdSpec_snd]


theorem nonempty_pullback_ker_pow_invModule_iso_of_sections {k : Type u} [Field k]
    {C Y : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) (hε : ε'.1 ≫ f = ε.1) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (((ε.1.ker) ^ n).invModule)
        ≅ (((ε'.1).ker) ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj (((ε.1.ker) ^ n).module)
        ≅ (((ε'.1).ker) ^ n).module) := by
  have : IsClosedImmersion ε.1 := isClosedImmersion_of_comp_eq_id c ε.1 ε.2
  exact Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso f ε.1 ε'.1 hε
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c) ε.1 ε.2)
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := y) ε'.1 ε'.2) n


theorem nonempty_pullback_fibreReading_iso
    {k : Type u} [Field k] {C Y T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (y : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated y] [SmoothOfRelativeDimension 1 y]
    (f : Y ⟶ C) [IsIso f]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ Y // p ≫ y = 𝟙 _}) (hε : ε'.1 ≫ f = ε.1)
    (t : T ⟶ Spec (CommRingCat.of k)) (x : Spec (CommRingCat.of k) ⟶ T) (hx : x ≫ t = 𝟙 _)
    (PL : (pullback c t).Modules) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback
            (pullback.lift (𝟙 C) (c ≫ x)
                (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]))).obj PL ⊗
          ((ε.1.ker) ^ d).invModule) ≅
      (Scheme.Modules.pullback (f ≫ toProdSpec c)).obj
          ((Scheme.Modules.pullback (baseChangeSnd c
              (⟨x, hx⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t))).obj PL) ⊗
        (((ε'.1).ker) ^ d).invModule) := by
  obtain ⟨e2⟩ := (nonempty_pullback_ker_pow_invModule_iso_of_sections c y f ε ε' hε d).1
  have e1 := (Scheme.Modules.pullbackComp f (pullback.lift (𝟙 C) (c ≫ x)
      (by rw [Category.id_comp, Category.assoc, hx, Category.comp_id]))).app PL ≪≫
    (Scheme.Modules.pullbackCongr
      (comp_lift_eq_comp_toProdSpec_baseChangeSnd c f t x hx _)).app PL ≪≫
    ((Scheme.Modules.pullbackComp (f ≫ toProdSpec c)
      (baseChangeSnd c (⟨x, hx⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t))).app PL).symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ tensorIso e1 e2⟩


theorem isInvertible_pointsSubBasepointModule {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)) :
    Scheme.Modules.IsInvertible (pointsSubBasepointModule (a := c) ε Ps) := by
  induction Ps with
  | nil => exact Scheme.Modules.isInvertible_unit _
  | cons P Ps ih =>
      rw [pointsSubBasepointModule_cons]
      exact ((RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor
        (RelEffCartierDiv.isInvertible_I _).isInvertible_module).tensor ih

end AlgebraicGeometry.RelPicard.PtsCoreGlue

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace PtsCoreGlue
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]

theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F)
        = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]

end AlgebraicGeometry.RelPicard.PtsCoreGlue

open AlgebraicGeometry.RelPicard.PtsCoreGlue in
theorem _root_.AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_abelJacobi_of_curveModel
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    {F : Type v} [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (M : CurveModel k F) (e : M.C ≅ C) (he : e.hom ≫ c = M.toBase)
    (ε' : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (hε' : ε'.1 ≫ e.hom = ε.1) :
    let : GrpObj (Over.mk J.toBase) :=
      (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J
        from h).grpObj
    ∃ pts : Pic0 k F ≃ (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase),
      (∀ a b : Pic0 k F, pts (a + b) = pts a * pts b) ∧
      (∀ (l : List {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _})
        (Dv : Divisor.degZero (K := k) (F := F)),
        (Dv : Divisor k F) = (l.map fun P => Finsupp.single (M.pointEquivPlace P) (1 : ℤ)).sum
            - (l.length : ℤ) • Finsupp.single (M.pointEquivPlace ε') 1 →
        Nonempty ((h.poincare.pullbackAlong
            ⟨(pts (Pic0.mk Dv)).left, Over.w (pts (Pic0.mk Dv))⟩).L ≅
          pointsSubBasepointModule (a := c) ε
            (l.map fun P => (⟨P.1 ≫ e.hom, (Category.assoc _ _ _).trans
                ((congrArg (P.1 ≫ ·) he).trans P.2)⟩ :
              SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)))) ∧
      ∀ (Dv : Divisor.degZero (K := k) (F := F)) (d : ℕ) (𝒱 : C.TwoAffineOpenCover),
        Nontrivial (𝒱.sectionsOf c
          ((Scheme.Modules.pullback
              (pullback.lift (𝟙 C) (c ≫ (pts (Pic0.mk Dv)).left)
                (((Category.id_comp c).trans (Category.comp_id c).symm).trans
                  ((congrArg (c ≫ ·) (Over.w (pts (Pic0.mk Dv)))).symm.trans
                    (Category.assoc c _ _).symm)))).obj h.poincare.L ⊗
            ((ε.1.ker) ^ d).invModule)).H0 ↔
          0 < ell ((Dv : Divisor k F) + Finsupp.single (M.pointEquivPlace ε') (d : ℤ))  := by
  intro representingGroup
  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J := h
  let pt : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase)
      → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) J.toBase :=
    fun a => ⟨a.left, by have w := Over.w a; simp only [Over.mk_left, Over.mk_hom] at w; exact w⟩
  let P : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase)
      → (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules :=
    fun a => (h.poincare.pullbackAlong (pt a)).L
  let g : M.C ⟶ pullback c (𝟙 (Spec (CommRingCat.of k))) := e.hom ≫ toProdSpec c
  have : IsIso (toProdSpec c) := ⟨⟨pullback.fst c (𝟙 _), toProdSpec_fst c, fst_toProdSpec c⟩⟩
  have : IsIso g := IsIso.comp_isIso
  let Lmod : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → M.C.Modules :=
    fun a => (Scheme.Modules.pullback g).obj (P a)
  obtain ⟨cl, hcl_iso, hcl_tensor, hcl_one, hcl_pt, hcl_num⟩
    := AlgebraicCurve.CurveModel.exists_divisorClassMap M
  let Φ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → Pic k F
    := fun a => cl (Lmod a)
  have hPinv : ∀ a, Scheme.Modules.IsInvertible (P a)
    := fun a => (h.poincare.pullbackAlong (pt a)).isInvertible
  have hLinv : ∀ a, Scheme.Modules.IsInvertible (Lmod a) := fun a => (hPinv a).pullback g
  have hΦmul : ∀ a b, Φ (a * b) = Φ a + Φ b := by
    intro a b
    obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso hG a b
    have i' : Lmod (a * b) ≅ Lmod a ⊗ Lmod b :=
      (Scheme.Modules.pullback g).mapIso i ≪≫ Scheme.Modules.pullbackTensorObjIso g _ _
    change cl (Lmod (a * b)) = cl (Lmod a) + cl (Lmod b)
    rw [hcl_iso _ _ (hLinv _) ⟨i'⟩, hcl_tensor _ _ (hLinv a) (hLinv b)]
  have hΦone : Φ 1 = 0 := by
    obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    have i' : Lmod 1 ≅ 𝟙_ M.C.Modules :=
      (Scheme.Modules.pullback g).mapIso i ≪≫ Scheme.Modules.pullbackTensorUnitObjIso g
    change cl (Lmod 1) = 0
    rw [hcl_iso _ _ (hLinv _) ⟨i'⟩, hcl_one]
  have hcutP : ∀ a, FibrewiseAlgEquivZero (h.poincare.pullbackAlong (pt a)) := fun a =>
    (algEquivZeroCut c ε).pullback_mem _ _ (pt a) _ h.poincare_mem
  let s₁ : pullback c (𝟙 (Spec (CommRingCat.of k))) ⟶
      pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of k)))) (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (𝟙 _) (pullback.snd c (𝟙 _)) (by rw [Category.id_comp, Category.comp_id])
  have hs₁fst : s₁ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hs₁snd : s₁ ≫ fibreAt c (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) = pullback.snd c (𝟙 _) := by
    change s₁ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _
  have hιsnd : toProdSpec c ≫ pullback.snd c (𝟙 _) = c := by
    change pullback.lift (𝟙 C) c (by rw [Category.id_comp, Category.comp_id]) ≫ pullback.snd _ _ = c
    exact pullback.lift_snd _ _ _
  have hg_base : (g ≫ s₁) ≫ fibreAt c (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) = M.toBase := by
    rw [Category.assoc, hs₁snd, show g = e.hom ≫ toProdSpec c from rfl, Category.assoc, hιsnd, he]
  have hι_base : (toProdSpec c ≫ s₁) ≫ fibreAt c (𝟙 _) (𝟙 (Spec (CommRingCat.of k))) = c := by
    rw [Category.assoc, hs₁snd, hιsnd]
  have hg_fac : (g ≫ s₁) ≫ pullback.fst _ _ = g := by rw [Category.assoc, hs₁fst, Category.comp_id]
  have hι_fac : (toProdSpec c ≫ s₁) ≫ pullback.fst _ _ = toProdSpec c
    := by rw [Category.assoc, hs₁fst, Category.comp_id]
  have halgM : ∀ a, IsAlgEquivZero M.toBase (Lmod a) := fun a =>
    (((hcutP a) k (𝟙 _)).pullback (g ≫ s₁) hg_base).of_iso
      (pullbackCompCompIso g s₁ _ g hg_fac (P a))
  let LC : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → C.Modules :=
    fun a => (Scheme.Modules.pullback (toProdSpec c)).obj (P a)
  have hLCinv : ∀ a, Scheme.Modules.IsInvertible (LC a) := fun a => (hPinv a).pullback _
  have halgC : ∀ a, IsAlgEquivZero c (LC a) := fun a =>
    (((hcutP a) k (𝟙 _)).pullback (toProdSpec c ≫ s₁) hι_base).of_iso
      (pullbackCompCompIso _ s₁ _ _ hι_fac (P a))
  have hLmodLC : ∀ a, Nonempty (Lmod a ≅ (Scheme.Modules.pullback e.hom).obj (LC a)) := fun a =>
    ⟨((Scheme.Modules.pullbackComp e.hom (toProdSpec c)).app (P a)).symm⟩
  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top
    M.toBase M.finset_subset_affineOpen
  let 𝒱M : M.C.TwoAffineOpenCover :=
    { U0 := U, U1 := V, isAffineOpen_U0 := hU, isAffineOpen_U1 := hV,
      sup_eq_top := hsup, isAffineOpen_inf := hUV }
  have hdeg0 : ∀ a (D : Divisor k F), (QuotientAddGroup.mk D : Pic k F) = Φ a
      → Divisor.degree D = 0 := by
    intro a D hD
    obtain ⟨-, -, -, hχ⟩ := hcl_num 𝒱M (Lmod a) (hLinv a) D hD
    have hcc := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq M.toBase 𝒱M (Lmod a) (𝟙_ _) (hLinv a)
      (Scheme.Modules.isInvertible_unit _) (halgM a)
    have hcongr := eulerChar_congr M.toBase 𝒱M (ρ_ (Lmod a))
    linarith
  let Φ' : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) → Pic0 k F := fun a =>
    Pic0.mk ⟨(Φ a).out, Divisor.mem_degZero.mpr (hdeg0 a _ (QuotientAddGroup.out_eq' (Φ a)))⟩
  have hΦ'Φ : ∀ a (Dv : Divisor.degZero (K := k) (F := F)),
      Φ' a = Pic0.mk Dv ↔ Φ a = QuotientAddGroup.mk (Dv : Divisor k F) := by
    intro a Dv
    rw [pic0_mk_eq_iff]
    change (QuotientAddGroup.mk (Φ a).out : Pic k F) = _ ↔ _
    rw [QuotientAddGroup.out_eq']
  have hΦ'mul : ∀ a b, Φ' (a * b) = Φ' a + Φ' b := by
    intro a b
    rw [← Pic0.mk_add, hΦ'Φ, AddSubgroup.coe_add, QuotientAddGroup.mk_add]
    change Φ (a * b) = (QuotientAddGroup.mk (Φ a).out : Pic k F) + QuotientAddGroup.mk (Φ b).out
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq', hΦmul]
  have : IsSeparated c := inferInstance
  have hker : ∀ a, Φ a = 0 → a = 1 := by
    intro a ha
    obtain ⟨𝒱C⟩ := nonempty_twoAffineOpenCover_of_iso e.symm 𝒱M
    obtain ⟨𝒱n, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      M.toBase c e he 𝒱C (LC a) (Lmod a) (hLmodLC a).some
    have h0 : (QuotientAddGroup.mk (0 : Divisor k F) : Pic k F) = Φ a
      := by rw [ha, QuotientAddGroup.mk_zero]
    obtain ⟨hfinL, -, hL0, -⟩ := hcl_num 𝒱n (Lmod a) (hLinv a) 0 h0
    have h1 : (QuotientAddGroup.mk (0 : Divisor k F) : Pic k F) = cl (𝟙_ M.C.Modules)
      := by rw [hcl_one, QuotientAddGroup.mk_zero]
    obtain ⟨hfin1, -, h10, -⟩ := hcl_num 𝒱n (𝟙_ M.C.Modules) (Scheme.Modules.isInvertible_unit _)
      0 h1
    have := hfin1
    have hpos : 0 < Module.finrank k (𝒱n.sectionsOf M.toBase (Lmod a)).H0 := by
      rw [hL0, ← h10]
      have := nontrivial_H0_tensorUnit (X := M.C) M.toBase 𝒱n
      exact Module.finrank_pos
    have : Nontrivial (𝒱n.sectionsOf M.toBase (Lmod a)).H0 := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨u, v, huv⟩ := (inferInstance : Nontrivial (𝒱n.sectionsOf M.toBase (Lmod a)).H0)
    have hntC : Nontrivial (𝒱C.sectionsOf c (LC a)).H0
      := ⟨e0 u, e0 v, fun hh => huv (e0.injective hh)⟩
    obtain ⟨s, hs⟩ := exists_hom_ne_zero_of_nontrivial_H0 c 𝒱C (LC a) hntC
    obtain ⟨iC⟩ := IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero c 𝒱C (hLCinv a) (halgC a) s hs
    have iP : P a ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 (Spec (CommRingCat.of k)))).L :=
      isoPullbackInvPullbackObj (toProdSpec c) (P a) ≪≫
        (Scheme.Modules.pullback (inv (toProdSpec c))).mapIso iC ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso (inv (toProdSpec c))
    obtain ⟨i1⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    have hpt : pt a = pt 1 := h.ext_of_iso (𝟙 _) (pt a) (pt 1) ⟨iP ≪≫ i1.symm⟩
    exact Over.OverMorphism.ext (congrArg Subtype.val hpt)
  have hΦ'inj : Function.Injective Φ' := by
    intro a b hab
    have h2 : Φ a = Φ b := by
      have := (hΦ'Φ a
        ⟨(Φ b).out, Divisor.mem_degZero.mpr (hdeg0 b _ (QuotientAddGroup.out_eq' (Φ b)))⟩).mp hab
      rw [this]
      exact QuotientAddGroup.out_eq' (Φ b)
    have h3 : Φ (a * b⁻¹) = 0 := by
      have h4 : Φ (b * b⁻¹) = 0 := by rw [mul_inv_cancel, hΦone]
      rw [hΦmul] at h4 ⊢
      rw [h2]; exact h4
    have := hker _ h3
    rw [mul_inv_eq_one] at this
    exact this
  have : IsSeparated M.toBase := inferInstance
  have hkerinv : ∀ (P : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (n : ℕ),
      (((P.1).ker) ^ n).IsInvertible := fun P n =>
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) P.1 P.2).pow n
  have hcl_foldr : ∀ Ps' : List {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
      Scheme.Modules.IsInvertible
          (Ps'.foldr (fun P A => ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) ⊗ A)
            (𝟙_ M.C.Modules)) ∧
        cl (Ps'.foldr (fun P A => ((((P.1).ker) ^ 1).invModule ⊗ (((ε'.1).ker) ^ 1).module) ⊗ A)
            (𝟙_ M.C.Modules)) =
          QuotientAddGroup.mk ((Ps'.map fun P => Finsupp.single (M.pointEquivPlace P) (1 : ℤ)).sum
            - (Ps'.length : ℤ) • Finsupp.single (M.pointEquivPlace ε') 1) := by
    intro Ps'
    induction Ps' with
    | nil =>
        refine ⟨Scheme.Modules.isInvertible_unit _, ?_⟩
        simp only [List.foldr_nil, List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero,
          zero_smul, sub_zero,
          QuotientAddGroup.mk_zero]
        exact hcl_one
    | cons P Ps' ih =>
        obtain ⟨ihinv, ihcl⟩ := ih
        have hA : Scheme.Modules.IsInvertible ((((P.1).ker) ^ 1).invModule
            ⊗ (((ε'.1).ker) ^ 1).module) :=
          (hkerinv P 1).isInvertible_invModule.tensor (hkerinv ε' 1).isInvertible_module
        refine ⟨hA.tensor ihinv, ?_⟩
        rw [List.foldr_cons, hcl_tensor _ _ hA ihinv, hcl_tensor _ _
            (hkerinv P 1).isInvertible_invModule
          (hkerinv ε' 1).isInvertible_module, (hcl_pt P 1).1, (hcl_pt ε' 1).2, ihcl]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ,
            one_smul, add_smul]
        rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
        congr 1
        abel
  have hwit : ∀ l : List {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
      ∃ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase,
        Nonempty (P a ≅ pointsSubBasepointModule (a := c) ε
          (l.map fun P => (⟨P.1 ≫ e.hom, (Category.assoc _ _ _).trans
              ((congrArg (P.1 ≫ ·) he).trans P.2)⟩ :
            SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))) ∧
        Φ a = QuotientAddGroup.mk ((l.map fun P => Finsupp.single (M.pointEquivPlace P) (1 : ℤ)).sum
            - (l.length : ℤ) • Finsupp.single (M.pointEquivPlace ε') 1) := by
    intro Ps'
    let Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :=
      Ps'.map fun P => (⟨P.1 ≫ e.hom, (Category.assoc _ _ _).trans
          ((congrArg (P.1 ≫ ·) he).trans P.2)⟩ :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    have hNinv : Scheme.Modules.IsInvertible (pointsSubBasepointModule (a := c) ε Ps) :=
      isInvertible_pointsSubBasepointModule c ε Ps
    obtain ⟨rig⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
      ((Scheme.Modules.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).obj
        (pointsSubBasepointModule (a := c) ε Ps))
      (hNinv.pullback _)
    let N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))) :=
      { L := pointsSubBasepointModule (a := c) ε Ps, isInvertible := hNinv, rigidified := ⟨rig⟩ }
    have hcut : (algEquivZeroCut c ε).P (𝟙 _) N :=
      RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule N Ps (Iso.refl _)
    let a' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) J.toBase := h.classify (𝟙 _) N hcut
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase := Over.homMk a'.1 a'.2
    have hpa : pt a = a' := Subtype.ext rfl
    obtain ⟨iN⟩ := h.classify_spec (𝟙 _) N hcut
    have iP : P a ≅ pointsSubBasepointModule (a := c) ε Ps := by
      change (h.poincare.pullbackAlong (pt a)).L ≅ _
      rw [hpa]
      exact iN
    obtain ⟨iF⟩ := nonempty_pullback_pointsSubBasepointModule_iso_foldr c M.toBase e.hom he
      ε ε' hε' Ps'
    refine ⟨a, ⟨iP⟩, ?_⟩
    change cl (Lmod a) = _
    rw [hcl_iso _ _ (hLinv a) ⟨(Scheme.Modules.pullback g).mapIso iP ≪≫ iF⟩, (hcl_foldr Ps').2]
  have hΦ'surj : Function.Surjective Φ' := by
    intro ξ
    obtain ⟨Dv, rfl⟩ := Pic0.mk_surjective ξ
    obtain ⟨l, hl⟩ := AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
      (M.pointEquivPlace ε') (Dv : Divisor k F) (Divisor.mem_degZero.mp Dv.2)
    obtain ⟨a, -, ha⟩ := hwit (l.map M.pointEquivPlace.symm)
    refine ⟨a, ?_⟩
    rw [hΦ'Φ, ha, pic_mk_eq_iff]
    have hmap : (l.map M.pointEquivPlace.symm).map
        (fun P => Finsupp.single (M.pointEquivPlace P) (1 : ℤ)) =
        l.map fun v => Finsupp.single v (1 : ℤ) := by
      rw [List.map_map]
      congr 1
      funext v
      simp only [Function.comp, Equiv.apply_symm_apply]
    have hlen : (l.map M.pointEquivPlace.symm).length = l.length := List.length_map _
    rw [hmap, hlen]
    have := Divisor.principal.neg_mem hl
    rw [neg_sub] at this
    exact this
  let Ψ : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase) ≃ Pic0 k F
    := Equiv.ofBijective Φ' ⟨hΦ'inj, hΦ'surj⟩
  refine ⟨Ψ.symm, fun x y => ?_, fun l Dv hDv => ?_, fun Dv d 𝒱 => ?_⟩
  · apply Ψ.injective
    change Φ' (Ψ.symm (x + y)) = Φ' (Ψ.symm x * Ψ.symm y)
    rw [hΦ'mul]
    change Ψ (Ψ.symm (x + y)) = Ψ (Ψ.symm x) + Ψ (Ψ.symm y)
    simp only [Equiv.apply_symm_apply]
  · obtain ⟨a, ⟨iP⟩, ha⟩ := hwit l
    have ha' : Φ' a = Pic0.mk Dv := by rw [hΦ'Φ, ha, hDv]
    have hΨ : Ψ.symm (Pic0.mk Dv) = a := by
      rw [Equiv.symm_apply_eq]
      exact ha'.symm
    rw [hΨ]
    exact ⟨iP⟩
  · let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase := Ψ.symm (Pic0.mk Dv)
    have ha : Φ a = QuotientAddGroup.mk (Dv : Divisor k F)
      := (hΦ'Φ a Dv).mp (Ψ.apply_symm_apply (Pic0.mk Dv))
    obtain ⟨iG⟩ := nonempty_pullback_fibreReading_iso c M.toBase e.hom ε ε' hε'
      J.toBase a.left (pt a).2 h.poincare.L d
    obtain ⟨𝒱n, -, -, ⟨e0⟩, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      M.toBase c e he 𝒱 _
      (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule) iG.symm
    have hinvG : Scheme.Modules.IsInvertible (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule) :=
      (hLinv a).tensor (hkerinv ε' d).isInvertible_invModule
    have hclG : (QuotientAddGroup.mk ((Dv : Divisor k F) +
          Finsupp.single (M.pointEquivPlace ε') (d : ℤ))
          : Pic k F) =
        cl (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule) := by
      rw [hcl_tensor _ _ (hLinv a) (hkerinv ε' d).isInvertible_invModule, (hcl_pt ε' d).1,
        QuotientAddGroup.mk_add,
        Finsupp.smul_single, Nat.smul_one_eq_cast]
      change _ = Φ a + _
      rw [ha]
    obtain ⟨hfin, -, hh0, -⟩ := hcl_num 𝒱n _ hinvG _ hclG
    have := hfin
    constructor
    · rintro ⟨u, v, huv⟩
      have : Nontrivial (𝒱n.sectionsOf M.toBase (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule)).H0 :=
        ⟨e0.symm u, e0.symm v, fun hh => huv (e0.symm.injective hh)⟩
      have hpos : 0 < Module.finrank k (𝒱n.sectionsOf M.toBase
          (Lmod a ⊗ (((ε'.1).ker) ^ d).invModule)).H0 :=
        Module.finrank_pos
      rwa [hh0] at hpos
    · intro hpos
      rw [← hh0] at hpos
      obtain ⟨u, v, huv⟩ := Module.nontrivial_of_finrank_pos hpos
      exact ⟨e0 u, e0 v, fun hh => huv (e0.injective hh)⟩
end
end JacobianVarieties.Picard.Proofs.Exists_pic0_equiv_points_abelJacobi_of_curveModel
end ProofImplementation

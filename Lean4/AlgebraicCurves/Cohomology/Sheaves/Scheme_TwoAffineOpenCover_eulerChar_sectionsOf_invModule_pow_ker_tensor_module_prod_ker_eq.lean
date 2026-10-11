/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_eulerChar_sectionsOf_invModule_pow_ker_tensor_module_prod_ker_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isFinite_and_finrank_mul_subscheme_comp_eq_add
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import AlgebraicCurves.Models.CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import AlgebraicCurves.Geometry.Nonempty_algEquiv_functionField_of_iso
import AlgebraicCurves.Cohomology.RiemannRoch.GenusFF_eq_of_algEquiv
import AlgebraicCurves.Cohomology.Cech.Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed

/-!
# Scheme Two Affine Open Cover euler Char sections Of inv Module pow ker tensor module prod
ker eq
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicTwoAffineCover
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  isScalarTower
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instLinearOrder
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  module
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instFintype
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  addCommGroup
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instDecidableEqIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  moduleSections
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.SheafOfModules in
attribute [-instance]
  isIso_ihomModelToIhom
open AlgebraicGeometry.Scheme.OrderedAffineCoverOf in
attribute [-instance]
  instDecidableEqIdx
  instFintype
  instLinearOrder
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  instSubsingletonObjZero
open AlgebraicGeometry.OModulePresheaf.Leray in
attribute [-instance]
  relAltC_scalarTower
  ker_relAltd_modΓ
  relAltC_modΓ
  biC_abGrp
  relAltH_modΓ
  ker_relAltd_smul
  relAltH_scalarTower
  relAltH_smul
  biC_module
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve in
attribute [-instance]
  instFundamentalIdentityOfSumRamificationInertia
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open AlgebraicCurve.SemilinearAut in
attribute [-instance]
  instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
open AlgebraicCurve.Pic0 in
attribute [-instance]
  instModuleZModTorsion
open AlgebraicCurve.SemilinearAut in
attribute [-instance]
  instSMulSubtypeProdRingAutMemSubgroupPlace
  instDistribMulActionTorsion
  instSMulSubtypeProdRingAutMemSubgroupPic0
  instSMulTorsion
  instMulActionSubtypeProdRingAutMemSubgroupPlace
  instSMulCommClassZModTorsion
  instMulSemiringActionSubtypeProdRingAutMemSubgroup
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
open _root_.AlgebraicCurve in
attribute [-instance]
  instHasLocalResidue_of_hasCanonicalLocalResidueK
  instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
open ModularCurve.KwF4gRRTate in
attribute [-instance]
  instAlgebraKAdicCompletionIntegers
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
open IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance] AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffHom.id_app
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
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
attribute [-simp] ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
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
attribute [-simp] ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

universe u

open scoped TensorProduct

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.AlgebraicCurve hiding genus cechDiff


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top
  IsProper Scheme.Hom GeometricallyIntegral IsFinite Spec IsIntegral Spec.map Scheme IsSeparated
  Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData
  Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap Scheme.IdealSheafData.IsInvertible
  Scheme.IdealSheafData.isInvertible_top Scheme.Hom.finrank_eq_zero_of_isEmpty
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
  Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
  Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add
  Scheme.Hom.isInvertible_ker_of_comp_eq_id
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
  Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed
  geometricallyIntegral_of_isAlgClosed)

namespace ChiFibGenus

open _root_.AlgebraicGeometry


section Generic

variable {R : Type u} [CommRing R] {𝒰 𝒰' : TwoChartCech.Cover.{u, u} R}
  (S : TwoChartCech.Sections.{u, u, u} 𝒰) (S' : TwoChartCech.Sections.{u, u, u} 𝒰')

theorem h0h1_of_equiv (g0 : S.M0 ≃ₗ[R] S'.M0) (g1 : S.M1 ≃ₗ[R] S'.M1) (g01 : S.M01 ≃ₗ[R] S'.M01)
    (h0 : ∀ m, S'.r0 (g0 m) = g01 (S.r0 m)) (h1 : ∀ m, S'.r1 (g1 m) = g01 (S.r1 m)) :
    Nonempty (S.H0 ≃ₗ[R] S'.H0) ∧ Nonempty (S.H1 ≃ₗ[R] S'.H1) := by
  let G : (S.M0 × S.M1) ≃ₗ[R] (S'.M0 × S'.M1) := g0.prodCongr g1
  have hG : ∀ p : S.M0 × S.M1, G p = (g0 p.1, g1 p.2) := fun p => rfl
  have hd : ∀ p, S'.cechDiff (G p) = g01 (S.cechDiff p) := by
    intro p
    rw [hG, TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub,
      h0, h1]
  refine ⟨⟨LinearEquiv.ofSubmodules G S.H0 S'.H0 ?_⟩, ⟨Submodule.Quotient.equiv _ _ g01 ?_⟩⟩
  · ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hd, hp, map_zero]
    · intro hq
      refine ⟨G.symm q, ?_, G.apply_symm_apply q⟩
      apply g01.injective
      rw [← hd, G.apply_symm_apply, hq, map_zero]
  · ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨G p, hd p⟩
    · rintro ⟨q, rfl⟩
      exact ⟨S.cechDiff (G.symm q), ⟨_, rfl⟩, by rw [← hd, G.apply_symm_apply]⟩

end Generic

section UnitEq

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶ Spec (.of
  R))

/-- Identifies sections of the structure module on the first affine open with ring sections. -/
noncomputable def idEquiv0 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M0 ≃ₗ[R]
      (𝒱.structureSheafSections x).M0 :=
  LinearEquiv.refl R ((𝒱.structureSheafSections x).M0)

/-- Identifies sections of the structure module on the second affine open with ring sections. -/
noncomputable def idEquiv1 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M1 ≃ₗ[R]
      (𝒱.structureSheafSections x).M1 :=
  LinearEquiv.refl R ((𝒱.structureSheafSections x).M1)

/-- Identifies sections of the structure module on the intersection with ring sections. -/
noncomputable def idEquiv01 :
    (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01 ≃ₗ[R]
      (𝒱.structureSheafSections x).M01 :=
  LinearEquiv.refl R ((𝒱.structureSheafSections x).M01)

theorem unit_equiv :
    Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
        (𝒱.structureSheafSections x).H0) ∧
      Nonempty ((𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
        (𝒱.structureSheafSections x).H1) := by
  refine h0h1_of_equiv _ _ (idEquiv0 𝒱 x) (idEquiv1 𝒱 x)
    (idEquiv01 𝒱 x) ?_ ?_
  · intro m; rfl
  · intro m
    change (1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) * _ = _
    exact one_mul ((𝒱.cover x).ρ1 m)

end UnitEq

theorem finrank_baseChange_self {K : Type u} [Field K] {A B : Type u} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (d : A →ₗ[K] B) :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank K (LinearMap.ker d) ∧
      Module.finrank K ((K ⊗[K] B) ⧸ LinearMap.range (d.baseChange K)) =
        Module.finrank K (B ⧸ LinearMap.range d) := by
  let eA := TensorProduct.lid K A
  let eB := TensorProduct.lid K B
  have hd : ∀ z, eB (d.baseChange K z) = d (eA z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      simp only [eA, eB, LinearMap.baseChange_tmul, TensorProduct.lid_tmul, map_smul]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  constructor
  · refine (LinearEquiv.ofSubmodules eA (LinearMap.ker (d.baseChange K)) (LinearMap.ker d)
      ?_).finrank_eq
    ext q
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [← hd, hp, map_zero]
    · intro hq
      refine ⟨eA.symm q, ?_, eA.apply_symm_apply q⟩
      apply eB.injective
      rw [hd, eA.apply_symm_apply, hq, map_zero]
  · refine (Submodule.Quotient.equiv _ _ eB ?_).finrank_eq
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
      exact ⟨eA p, (hd p).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨d.baseChange K (eA.symm q), ⟨_, rfl⟩, by rw [hd, eA.apply_symm_apply]⟩

theorem rr_of_cech (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec
  (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ) (𝒱 : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 =
      g) :
    (∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g) ∧
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L),
      ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by
  classical
  obtain ⟨-, ⟨eH1⟩⟩ := unit_equiv 𝒱 x
  rw [eH1.finrank_eq] at hg
  have : GeometricallyIntegral x := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed x
  have : IsIntegral (pullback x (Scheme.TwoAffineOpenCover.specMap K K)) := inferInstance
  obtain ⟨-, -, hk1⟩ := Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 x K
  obtain ⟨-, hb1⟩ := finrank_baseChange_self (𝒱.structureSheafSections x).cechDiff
  have hG : (by
      let := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) = g := by
    rw [← hk1, hb1]
    exact hg
  have hspec : Scheme.TwoAffineOpenCover.specMap K K = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have sq : IsPullback (𝟙 X) x x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [hspec]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  let eX : X ≅ pullback x (Scheme.TwoAffineOpenCover.specMap K K) := sq.isoPullback
  have heX : eX.hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = x :=
    sq.isoPullback_hom_snd
  have heX' : eX.inv ≫ x = pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) := by
    rw [Iso.inv_comp_eq]; exact heX.symm
  have huniq : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
    intro L _ _ M e he Kc g' hRR
    have h1 : g' = genusFF K L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
    have he2 : (e ≪≫ eX).hom ≫ pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K) = M.toBase :=
      by
      simp only [Iso.trans_hom, Category.assoc]
      rw [heX]; exact he
    have h2 : genusFF K L = (by
        let := (baseToFunctionField
          (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
        exact genusFF K (pullback x (Scheme.TwoAffineOpenCover.specMap K K)).functionField) := by
      let := M.functionFieldAlgebra
      let := (baseToFunctionField
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K))).toAlgebra
      obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
        (pullback.snd x (Scheme.TwoAffineOpenCover.specMap K K)) (e ≪≫ eX) he2
      exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)
    rw [h1, h2, hG]
  refine ⟨huniq, ?_⟩
  obtain ⟨L, _, _, M, e, he, Kc, g₀, hRR⟩ :=
    exists_curveModel_riemannRoch_of_isAlgClosed K x K (Scheme.TwoAffineOpenCover.specMap K K)
  have he' : (e ≪≫ eX.symm).hom ≫ x = M.toBase := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [heX']; exact he
  have h3 : g₀ = g := huniq L M (e ≪≫ eX.symm) he' Kc g₀ hRR
  subst h3
  exact ⟨L, inferInstance, inferInstance, M, e ≪≫ eX.symm, he', Kc, hRR⟩

end AlgebraicGeometry.ChiFibGenus

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (SmoothOfRelativeDimension Scheme.IdealSheafData.one_eq_top
  IsProper Scheme.Hom GeometricallyIntegral IsFinite Spec IsIntegral Spec.map Scheme IsSeparated
  Spec.map_id Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData
  Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap Scheme.IdealSheafData.IsInvertible
  Scheme.IdealSheafData.isInvertible_top Scheme.Hom.finrank_eq_zero_of_isEmpty
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
  Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
  Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add
  Scheme.Hom.isInvertible_ker_of_comp_eq_id
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
  Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed
  geometricallyIntegral_of_isAlgClosed)

namespace ChiFib

open _root_.AlgebraicGeometry


theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem eulerChar_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
      (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  rw [e0.finrank_eq, e1.finrank_eq]

theorem prod_ker {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] (𝒱 : X.TwoAffineOpenCover)
    {n : ℕ} (v : Fin n → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) (s : Finset (Fin n)) :
    (∏ j ∈ s, (v j).1.ker).IsInvertible ∧
      ∃ _ : IsFinite ((∏ j ∈ s, (v j).1.ker).subschemeι ≫ x),
        ∀ y, ((∏ j ∈ s, (v j).1.ker).subschemeι ≫ x).finrank y = s.card := by
  classical
  have : IsSeparated x := inferInstance
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, Scheme.IdealSheafData.one_eq_top]
    exact ⟨Scheme.IdealSheafData.isInvertible_top, inferInstance,
      fun y => Scheme.Hom.finrank_eq_zero_of_isEmpty _ y⟩
  | insert j s hj ih =>
    obtain ⟨hJ, hfin, hdeg⟩ := ih
    have hq : (v j).1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (v j).1 (v j).2
    obtain ⟨hfin1, hdeg1, -, -⟩ :=
      Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (v j).1 (v j).2 1
    rw [pow_one] at hfin1 hdeg1
    have := hfin; have := hfin1
    have H := fun y =>
      Scheme.IdealSheafData.IsInvertible.isFinite_and_finrank_mul_subscheme_comp_eq_add x 𝒱 hq hJ y
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    refine ⟨hq.mul hJ, (H (IsLocalRing.closedPoint K)).1, fun y => ?_⟩
    rw [(H y).2, hdeg1 y, hdeg y, add_comm]

end AlgebraicGeometry.ChiFib

end
end AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicTwoAffineCover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicTwoAffineCover
universe u
open scoped _root_.TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.AlgebraicCurve hiding genus cechDiff


open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicTwoAffineCover in
open AlgebraicGeometry.ChiFib in
theorem eulerChar_sectionsOf_invModule_pow_ker_tensor_module_prod_ker_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ) (𝒱₀ : X.TwoAffineOpenCover)
    (hg : Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H1 = g)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ x = 𝟙 _) (r : ℕ)
    {n : ℕ} (v : Fin n → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})
    (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank K (𝒱.sectionsOf x (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H0 :
      ℤ) -
        Module.finrank K (𝒱.sectionsOf x (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H1 =
      1 - g + r - n := by
  classical
  have : IsSeparated x := inferInstance
  have hgu : Module.finrank K (𝒱₀.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1
    = g := hg
  obtain ⟨hgU, -⟩ := AlgebraicGeometry.ChiFibGenus.rr_of_cech K x g 𝒱₀ hgu
  obtain ⟨hH1, hH0⟩ :=
    Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K x g hgU 𝒱
  change Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 = g at hH1
  change Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 = 1 at hH0
  have hpk : p.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp
  have hIr : (p.ker ^ r).IsInvertible := hpk.pow r
  have hTw : Scheme.Modules.IsInvertible (p.ker ^ r).invModule := hIr.isInvertible_invModule
  obtain ⟨hZ, hdegr, -, -⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id p
    hp r
  have hA := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq x hIr hZ
    hdegr
    (𝟙_ _) (Scheme.Modules.isInvertible_unit _) 𝒱
  have hA' := eulerChar_congr x 𝒱 (λ_ ((p.ker ^ r).invModule))
  obtain ⟨hJ, hJfin, hJdeg⟩ := prod_ker x 𝒱 v Finset.univ
  have hN : Scheme.Modules.IsInvertible (∏ j, (v j).1.ker).module := hJ.isInvertible_module
  have hTN : Scheme.Modules.IsInvertible ((p.ker ^ r).invModule ⊗ (∏ j, (v j).1.ker).module) :=
    hTw.tensor hN
  have hdegn : ∀ y, ((∏ j, (v j).1.ker).subschemeι ≫ x).finrank y = n := fun y => by
    rw [hJdeg y, Finset.card_univ, Fintype.card_fin]
  have hB := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq x hJ hJfin
    hdegn
    ((p.ker ^ r).invModule ⊗ (∏ j, (v j).1.ker).module) hTN 𝒱
  have eN : (∏ j, (v j).1.ker).module ⊗ (∏ j, (v j).1.ker).invModule ≅ 𝟙_ X.Modules :=
    (hN.dual).2.some
  have hB' := eulerChar_congr x 𝒱
    (α_ ((p.ker ^ r).invModule) ((∏ j, (v j).1.ker).module) ((∏ j, (v j).1.ker).invModule) ≪≫
      whiskerLeftIso ((p.ker ^ r).invModule) eN ≪≫ ρ_ ((p.ker ^ r).invModule))
  omega
end AlgebraicGeometry.Scheme.TwoAffineOpenCover
end ProofImplementation

open AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
open AlgebraicCurve.CurveModel in
attribute [-instance]
  isProper
  isIntegral
  smooth
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
open AlgebraicCurve.Divisor in
attribute [-instance]
  instDistribMulActionAlgEquiv
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instSMulAlgEquiv
  instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
open AlgebraicCurve.Pic0 in
attribute [-instance]
  instDistribMulActionAlgEquiv
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instAlgebraSubtypeMemValuationSubringToValuationSubring
  instMulActionAlgEquiv
open AlgebraicCurve.Pic0 in
attribute [-instance]
  instSMulAlgEquiv
open AlgebraicGeometry.RelEffCartierDiv in
attribute [-instance]
  subsingleton_of_degree_zero
  isIso_subschemeIota_snd_of_degree_one
open AlgebraicGeometry in
attribute [-instance]
  isIso_ker_graphOver_subschemeIota_snd
  isClosedImmersion_graphOver
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  isScalarTower
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instLinearOrder
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  module
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instFintype
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  addCommGroup
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instDecidableEqIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  moduleSections
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.SheafOfModules in
attribute [-instance]
  isIso_ihomModelToIhom
open AlgebraicGeometry.Scheme.OrderedAffineCoverOf in
attribute [-instance]
  instDecidableEqIdx
  instFintype
  instLinearOrder
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  instSubsingletonObjZero
open AlgebraicGeometry.OModulePresheaf.Leray in
attribute [-instance]
  relAltC_scalarTower
  ker_relAltd_modΓ
  relAltC_modΓ
  biC_abGrp
  relAltH_modΓ
  ker_relAltd_smul
  relAltH_scalarTower
  relAltH_smul
  biC_module
open DoubleComplex in
attribute [-instance]
  instModuleE₂I
open DoubleComplex.Bounded in
attribute [-instance]
  modR
open DoubleComplex in
attribute [-instance]
  instModuleE₂II
  instAddCommGroupE₂II
open DoubleComplex.Bounded in
attribute [-instance]
  abGrp
open DoubleComplex in
attribute [-instance]
  instAddCommGroupE₂I
open AlgebraicGeometry.ChowDatum in
attribute [-instance]
  hι_closed
open AlgebraicGeometry.ChowDatumProj in
attribute [-instance]
  hιN_closed
  hp_proper
open AlgebraicGeometry.ChowDatum in
attribute [-instance]
  hp_isoU
  hp_proper
open AlgebraicGeometry.ProjSpace in
attribute [-instance]
  algebraAway
  instIsProperProdOverπ
open AlgebraicGeometry.ChowDatumProj in
attribute [-instance]
  hp_isoU
open AlgebraicGeometry.ProjSpace in
attribute [-instance]
  isProper_π
open AlgebraicGeometry.ProjSpace in
attribute [-instance]
  finiteType_mvPolynomial
open ProjSpaceCech.GradedModule.H in
attribute [-instance]
  module
  addCommGroup
open ProjSpaceCech.GradedModule.sec in
attribute [-instance]
  instAdd
  instNeg
open ProjSpaceCech.GradedModule in
attribute [-instance]
  acg
open ProjSpaceCech.GradedModule.Frac in
attribute [-instance]
  setoid
open ProjSpaceCech.GradedModule in
attribute [-instance]
  modR
open ProjSpaceCech.GradedModule.sec in
attribute [-instance]
  instModule
  instAddCommGroup
  instZero
open ProjSpaceCech.GradedModule.Presentation in
attribute [-instance]
  fJ
open ProjSpaceCech.GradedModule.sec in
attribute [-instance]
  instSMul
open ProjSpaceCech.Twist.H in
attribute [-instance]
  module
open ProjSpaceCech.Idx in
attribute [-instance]
  instFintype
open ProjSpaceCech.Twist.H in
attribute [-instance]
  addCommGroup
open ProjSpaceCech.Idx in
attribute [-instance]
  instDecidableEq
open ProjSpaceCech.Twist.Mon in
attribute [-instance]
  instDecidableEq
open ProjSpaceCech.Twist.cochain in
attribute [-instance]
  instAddCommGroup
  instModule
open AlgebraicGeometry.SmoothOfRelativeDimension in
attribute [-instance]
  fiberToSpecResidueField
  pullback_snd
  pullback_fst
  smooth_one
open AlgebraicGeometry.SmoothProperCurve in
attribute [-instance]
  isIntegral_pullback_Spec_field
open AlgebraicGeometry.IsProper in
attribute [-instance]
  fiberToSpecResidueField
open AlgebraicCurve.IsCurveOver in
attribute [-instance]
  instNontrivialKaehler
  instFreeKaehler
  toHasPrincipalDivisors
  instFiniteResidue
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve in
attribute [-instance]
  instFundamentalIdentityOfSumRamificationInertia
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open AlgebraicCurve.SemilinearAut in
attribute [-instance]
  instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
open AlgebraicCurve.Pic0 in
attribute [-instance]
  instModuleZModTorsion
open AlgebraicCurve.SemilinearAut in
attribute [-instance]
  instSMulSubtypeProdRingAutMemSubgroupPlace
  instDistribMulActionTorsion
  instSMulSubtypeProdRingAutMemSubgroupPic0
  instSMulTorsion
  instMulActionSubtypeProdRingAutMemSubgroupPlace
  instSMulCommClassZModTorsion
  instMulSemiringActionSubtypeProdRingAutMemSubgroup
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
open _root_.AlgebraicCurve in
attribute [-instance]
  instHasLocalResidue_of_hasCanonicalLocalResidueK
  instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
open ModularCurve.KwF4gRRTate in
attribute [-instance]
  instAlgebraKAdicCompletionIntegers
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
open IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
open _root_.AlgebraicCurve in
attribute [-instance]
  instHasCanonicalLocalResidueK
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
open _root_.AlgebraicCurve in
attribute [-instance]
  instHasLocalResidue
open AlgebraicCurve.HasSeparableResidue in
attribute [-instance]
  of_perfectField_of_isCurveOver
  of_perfectField
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsLocalHom_restrictSubringHom
attribute [-instance] AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
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
  AlgebraicCurve.diagonalHom_apply
attribute [-simp] AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
attribute [-simp] AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
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
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
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
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
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
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
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
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

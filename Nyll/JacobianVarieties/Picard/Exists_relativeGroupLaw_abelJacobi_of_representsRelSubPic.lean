/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.JacobianVarieties.Picard.Exists_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Picard.BaseChange_points_mul_poincare_compat
import Nyll.JacobianVarieties.Picard.Exists_pic0_equiv_points_abelJacobi_of_curveModel
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_baseChange

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
# Abel–Jacobi maps and divisor classes on geometric fibres

Construct the group law and normalized Abel–Jacobi map from the represented Picard
functor, and identify geometric-fibre point differences with divisor classes.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AbelJacobiGroup
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

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicCurve
open _root_.AlgebraicGeometry.SmoothProperCurve

universe u v

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace DictGlue
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


theorem essFiniteType_of_curveModel {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) : Algebra.EssFiniteType K L := by
  let := M.functionFieldAlgebra
  have : Algebra.EssFiniteType K M.C.functionField :=
    AlgebraicCurve.essFiniteType_functionField M.toBase
  exact Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective


theorem isConnected_fibre_of_geometricallyConnected {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hgc : GeometricallyConnected f)
    :
    ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}) := by
  intro s
  have := hgc
  have h := isConnected_range (f.fiberι s).continuous
  rwa [Scheme.Hom.range_fiberι] at h


theorem nonempty_pullback_κ_inv_pointsSubBasepointModule_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    (xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K)) :
    Nonempty ((Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
        (pointsSubBasepointModule (a := baseChange R c K) (sectionBaseChange K ε) [xK]) ≅
      (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K))
          ((Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ specMap R K) xK.2).trans (Category.id_comp _)))))).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (specMap R K ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by
  have hx : (xK.1 ≫ pullback.fst c (specMap R K)) ≫ c =
      𝟙 (Spec (CommRingCat.of K)) ≫ specMap R K :=
    (Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ specMap R K) xK.2)))
  have hε : (specMap R K ≫ ε.1) ≫ c = 𝟙 (Spec (CommRingCat.of K)) ≫ specMap R K :=
    (Category.assoc _ _ _).trans
      (((congrArg (specMap R K ≫ ·) ε.2).trans (Category.comp_id _)).trans
      (Category.id_comp _).symm)
  have hpx : graphOver c (xK.1 ≫ pullback.fst c (specMap R K)) hx ≫
      (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv =
        graphOver (baseChange R c K) xK.1 xK.2 := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]
  have hpε : graphOver c (specMap R K ≫ ε.1) hε ≫
      (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv =
        graphOver (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2 := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc,
        sectionBaseChange_coe_fst]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]
  obtain ⟨ex⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv
    (graphOver (baseChange R c K) xK.1 xK.2)
    (graphOver c (xK.1 ≫ pullback.fst c (specMap R K)) hx) hpx
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint (baseChange R c K) xK.1 xK.2))
    (RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K)) hx))
    1).1
  obtain ⟨eε⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv
    (graphOver (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2)
    (graphOver c (specMap R K ≫ ε.1) hε) hpε
    (RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint (baseChange R c K)
        (sectionBaseChange K ε).1 (sectionBaseChange K ε).2))
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1) hε))
    1).2
  have ex' : (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
      (RelEffCartierDiv.ofPoint (baseChange R c K) xK.1 xK.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K)) hx).lineBundle :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _).symm)) ≪≫ ex ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _))
  have eε' : (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
      (RelEffCartierDiv.ofPoint (baseChange R c K)
        (sectionBaseChange K ε).1 (sectionBaseChange K ε).2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1) hε).idealModule :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _).symm)) ≪≫ eε ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))
  rw [pointsSubBasepointModule_cons, pointsSubBasepointModule_nil]
  exact ⟨(Scheme.Modules.pullback _).mapIso (ρ_ _) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    tensorIso ex' eε'⟩

end AlgebraicGeometry.RelPicard.DictGlue


open AlgebraicGeometry.RelPicard.DictGlue in
theorem _root_.AlgebraicGeometry.RelPicard.exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
    (R : Type u) [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw R D.toBase) (aj : SchemeHomOver c D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      (∀ (k : Type u) [Field k] (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
          (x : SchemeHomOver t c),
        Nonempty ((h.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans
                  ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by
  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  have : IsSeparated c := inferInstance
  obtain ⟨aj, hajε, hajP⟩ :=
    AlgebraicGeometry.RelPicard.exists_abelJacobi_of_representsRelSubPic R c ε D h
  refine ⟨hG.relativeGroupLaw, aj, ?_, ?_, hG.relativeGroupLaw_one, ?_, hajP, ?_⟩
  · exact ⟨hsm, hpr,
      isConnected_fibre_of_geometricallyConnected D.toBase hgc,
      ⟨hG.relativeGroupLaw⟩⟩
  · intro T t x y
    exact hG.relativeGroupLaw_isCommutative t x y
  · exact hajε
  · intro K _ _ i F _ _ _ M e _ he
    let : Algebra R K := i.toAlgebra
    have : Algebra.EssFiniteType K F :=
      essFiniteType_of_curveModel M
    obtain ⟨h', hP'⟩ :=
      AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange R c ε D h K
    obtain ⟨Θ, hΘ1, hΘmul, hΘP⟩ :=
      AlgebraicGeometry.RelPicard.baseChange_points_mul_poincare_compat R c ε D h K h' hP'
    let eI : M.C ≅ pullback c (specMap R K) := asIso e
    have heI : eI.hom ≫ baseChange R c K = M.toBase := he
    let εK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K) := sectionBaseChange K ε
    let ε'ₘ : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨εK.1 ≫ inv e, by
        rw [Category.assoc, ← heI]
        change εK.1 ≫ inv e ≫ e ≫ _ = _
        rw [IsIso.inv_hom_id_assoc]
        exact εK.2⟩
    have hε'ₘ : ε'ₘ.1 ≫ eI.hom = εK.1 := by
      change (εK.1 ≫ inv e) ≫ e = εK.1
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨pts, hadd, hAJ, -⟩ :=
      AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_abelJacobi_of_curveModel
        K (baseChange R c K) εK
        (D.baseChange K) h' M eI heI ε'ₘ hε'ₘ
    refine ⟨pts.trans Θ, fun x y => ?_, fun x s hs => ?_⟩
    · change Θ (pts (x + y)) = _
      rw [hadd, hΘmul]
      rfl
    · have hsK : s.1 ≫ e = εK.1 := by
        apply pullback.hom_ext
        · rw [Category.assoc]
          exact hs.trans (sectionBaseChange_coe_fst (R := R) K ε).symm
        · rw [Category.assoc]
          change s.1 ≫ e ≫ baseChange R c K = εK.1 ≫ pullback.snd _ _
          rw [he, s.2]
          exact (sectionBaseChange_coe_snd (R := R) K ε).symm
      have hsε : s = ε'ₘ := by
        apply Subtype.ext
        change s.1 = εK.1 ≫ inv e
        rw [← hsK, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      subst hsε
      have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
      have hDv : Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1 ∈
          Divisor.degZero (K := K) (F := F) := by
        rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1,
          hdeg1]
        rw [sub_self]
      refine ⟨⟨Finsupp.single (M.pointEquivPlace x) 1 -
        Finsupp.single (M.pointEquivPlace ε'ₘ) 1, hDv⟩, rfl, ?_⟩
      · obtain ⟨iAJ⟩ := hAJ [x] ⟨_, hDv⟩ (by
          change Finsupp.single (M.pointEquivPlace x) (1 : ℤ) -
            Finsupp.single (M.pointEquivPlace ε'ₘ) 1 = _
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            List.length_cons,
            List.length_nil, zero_add, Nat.cast_one, one_smul])
        let xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K) :=
          ⟨x.1 ≫ eI.hom, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) heI).trans x.2)⟩
        let xR : SchemeHomOver (specMap R K) c :=
          ⟨xK.1 ≫ pullback.fst c (specMap R K),
            (Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (· ≫ specMap R K) xK.2).trans (Category.id_comp _))))⟩
        obtain ⟨iR⟩ := hajP K (specMap R K) xR
        obtain ⟨iΘ⟩ := hΘP (pts (Pic0.mk ⟨_, hDv⟩))
        have key : Θ (pts (Pic0.mk ⟨Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace ε'ₘ) 1, hDv⟩)) =
            ⟨xR.1 ≫ aj.1,
              (Category.assoc _ _ _).trans ((congrArg (xR.1 ≫ ·) aj.2).trans xR.2)⟩ := by
          apply h.ext_of_iso (specMap R K)
          obtain ⟨iM⟩ :=
            nonempty_pullback_κ_inv_pointsSubBasepointModule_iso
              R c ε K xK
          exact ⟨iΘ ≪≫ (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 _)).inv).mapIso iAJ ≪≫
            iM ≪≫ iR.symm⟩
        change (Θ (pts (Pic0.mk ⟨_, hDv⟩))).1 = _
        rw [key]
        change ((x.1 ≫ e) ≫ pullback.fst c (specMap R K)) ≫ aj.1 = _
        simp only [Category.assoc]
end
end JacobianVarieties.Picard.Proofs.AbelJacobiGroup
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
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
attribute [-instance]
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
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
  PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
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
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelPicard.fst_toProdSpec
  AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc
attribute [-simp]
  AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc
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
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
attribute [-simp]
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
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
attribute [-simp]
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
attribute [-simp]
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
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
attribute [-simp]
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc

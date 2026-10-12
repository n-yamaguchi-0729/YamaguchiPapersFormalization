/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_fg_subalgebra_isPullback_prodStr_model
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces

/-!
# Noetherian models of rigidified bundles with trivial unit faces

Descend the group law and the three face trivializations through finite generated models.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NoetherianUnitFaces
attribute [-instance]
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
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
attribute [-instance]
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
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
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
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
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
attribute [-instance]
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  instTopologicallyFGOfFiniteType
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
attribute [-instance]
  AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AdicCompletion.instIsLocalRingMaximalIdeal
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp]
  IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of
  IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst_assoc
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd_assoc
  GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans
  AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst
  AlgebraicGeometry.SubalgebraStages.diagram_obj
attribute [-simp]
  AlgebraicGeometry.SubalgebraStages.leg_snd
  AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl
  AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt
  AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
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
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
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
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
attribute [-simp]
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
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard

end JacobianVarieties.Picard.Proofs.NoetherianUnitFaces

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

/-- Descend the group law and the three face trivializations through finite generated models. -/
theorem exists_isNoetherianRing_model_of_locIsoOnBase_unit_faces
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by
            rw [pullback.lift_fst_assoc, (L.one _).2]
            exact pullback.condition))).obj M.L) (𝟙_ _))
    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))
    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1
          (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _)) :
    ∃ (S₀ : Type) (_ : CommRing S₀) (_ : IsNoetherianRing S₀) (A₀ : Scheme) (f₀ : A₀ ⟶ Spec
      (CommRingCat.of S₀))
      (L₀ : RelativeGroupLaw S₀ f₀) (_ : AbelianSchemePropertyBundle S₀ f₀)
      (M₀ : RigidifiedLineBundle (prodStr f₀ f₀) ((L₀.prod L₀).one (𝟙 (Spec (CommRingCat.of S₀))))
        f₀),
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (L₀.one (prodStr f₀ f₀)).1 (pullback.fst f₀ f₀) (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by
              rw [pullback.lift_fst_assoc, (L₀.one _).2]
              exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift
            (pullback.lift (pullback.fst f₀ f₀) (L₀.one (prodStr f₀ f₀)).1 (by rw [(L₀.one _).2]))
            (pullback.snd f₀ f₀)
            (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M₀.L) (𝟙_ _) ∧
      LocIsoOnBase (prodStr f₀ f₀)
        ((Scheme.Modules.pullback
          (pullback.lift (𝟙 _) (L₀.one (prodStr f₀ f₀)).1
            (by rw [Category.id_comp, (L₀.one _).2]))).obj M₀.L) (𝟙_ _) ∧
      (Nonempty (M₀.L ≅ (RigidifiedLineBundle.unit (c := prodStr f₀ f₀) (ε := (L₀.prod L₀).one (𝟙
        (Spec (CommRingCat.of S₀)))) f₀).L) →
        Nonempty (M.L ≅ (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec
          (CommRingCat.of S)))) f).L)) := by
  obtain ⟨S₁, hS₁, A₁, f₁, L₁, _, hA₁, a, ha, hLa, M₁, hM⟩ :=
    exists_fg_subalgebra_isPullback_prodStr_model L hA M
  exact exists_isNoetherianRing_model_of_fg_subalgebra_model_of_locIsoOnBase_unit_faces
    L M h₁ h₂ h₃ S₁ hS₁ A₁ f₁ L₁ hA₁ a ha hLa M₁ hM
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_fg_subalgebra_isPullback_prodStr_model.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.Order.DirectedInverseSystem
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product
import Nyll.AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_isCommutative
import Nyll.AlgebraicCurves.Geometry.Schemes.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit

/-!
# Finitely generated models of the product rigidification

The group law, its product and a rigidified line bundle descend together to a
finitely generated subalgebra, with the cube pullback comparisons preserved.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FGProductModel
attribute [-instance]
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
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
attribute [-instance]
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
  ProjSpaceCech.Idx.instDecidableEq
attribute [-instance]
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
  AlgebraicCurve.CurveModel.finiteType_chartRing
attribute [-instance]
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
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans
  AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst
  AlgebraicGeometry.SubalgebraStages.diagram_obj
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
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
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
attribute [-simp]
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
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
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
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

noncomputable section

namespace CubeDescentAux

namespace FGStages

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

/-- Finitely generated subalgebras containing the chosen initial subalgebra. -/
abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

/-- The ring at a finitely generated stage. -/
abbrev G (i : Idx B) : Type := ↥i.1

/-- The inclusion homomorphism between ordered stages. -/
abbrev φ (i j : Idx B) (h : i ≤ j) :
    G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

/-- The homomorphism from a stage to the ambient ring. -/
abbrev g (i : Idx B) : G B i →+* A := algebraMap ↥i.1 A

/-- Transition maps preserve the underlying elements. -/
theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
/-- The structure map is the inclusion into the ambient ring. -/
theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.CubeDescentAux.FGStages.sup (i j : Idx B) :
    Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

export _root_.CubeDescentAux.FGStages (sup)

scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

/-- The initial finitely generated subalgebra is a stage. -/
theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

/-- The ambient ring is the direct limit of its finitely generated stages. -/
theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i))
  where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m},
      by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1),
    Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

/-- The structure maps are compatible with stage inclusions. -/
theorem g_comp_φ (i j : Idx B) (h : i ≤ j) : (g B j).comp (φ B i j h) = g B i := RingHom.ext fun _
  => rfl

private theorem _root_.CubeDescentAux.FGStages.isNoetherianRing [IsNoetherianRing A₀] (i : Idx B) :
    IsNoetherianRing (G B i) := by
  have := (Subalgebra.fg_iff_finiteType i.1).mp i.2.1
  exact Algebra.FiniteType.isNoetherianRing A₀ ↥i.1

export _root_.CubeDescentAux.FGStages (isNoetherianRing)

end FGStages

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages

/-- A base-change map preserving multiplication also preserves the identity. -/
theorem one_comp_eq_one {R R₁ : Type} [CommRing R] [CommRing R₁] {A A₁ : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)}
    (L : RelativeGroupLaw R f) (L₁ : RelativeGroupLaw R₁ f₁) (φ : R₁ →+* R)
    (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 ≫ a = (L₁.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have key : ∀ {t₁ : T ⟶ Spec (CommRingCat.of R₁)} (x : SchemeHomOver t₁ f₁), L₁.mul t₁ x x = x → x
    = L₁.one t₁ := by
    intro t₁ x hxx
    calc x = L₁.mul t₁ (L₁.mul t₁ (L₁.inv t₁ x) x) x := by rw [L₁.inv_mul_cancel, L₁.one_mul]
      _ = L₁.mul t₁ (L₁.inv t₁ x) (L₁.mul t₁ x x) := by rw [L₁.mul_assoc]
      _ = L₁.one t₁ := by rw [hxx, L₁.inv_mul_cancel]
  have h := hLa T t (L.one t) (L.one t)
  rw [L.one_mul] at h
  exact congrArg Subtype.val (key ⟨(L.one t).1 ≫ a,
    by rw [Category.assoc, ha.w, ← Category.assoc, (L.one t).2]⟩
    (Subtype.ext h.symm))

/-- The identity section is natural in the parameter scheme. -/
theorem one_coe_eq_comp_one {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

section Sections

variable {R R₁ : Type} [CommRing R] [CommRing R₁]

/-- The first projection of the rigidifying section. -/
@[reassoc]
theorem rigSection_fst {C T : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ pullback.fst c t = t ≫
      ε.1 :=
  pullback.lift_fst _ _ _

/-- The second projection of the rigidifying section. -/
@[reassoc]
theorem rigSection_snd {C T : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ pullback.snd c t = 𝟙 T
      :=
  pullback.lift_snd _ _ _

/-- The rigidifying section lies over the parameter structure map. -/
theorem rigSection_fst_comp {C T : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : rigSection c t ε ≫ (pullback.fst c t ≫ c)
      = t := by
  rw [← Category.assoc, rigSection_fst, Category.assoc, ε.2, Category.comp_id]

variable {A T A₁ X₁ : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of
  R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
  (f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)) (g₁ : X₁ ⟶ Spec (CommRingCat.of R₁))
  (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₁))) f₁)
  (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₁)) (a : A ⟶ A₁) (u : T ⟶ X₁)
  (e₁ : f ≫ ι = a ≫ f₁) (e₂ : t ≫ ι = u ≫ g₁) (hε : ε.1 ≫ a = ι ≫ ε₁.1)

include hε in
/-- The rigidifying section commutes with the induced pullback map. -/
theorem rigSection_comp_pullbackMap :
    rigSection f t ε ≫ pullback.map f t f₁ g₁ a u ι e₁ e₂ = u ≫ rigSection f₁ g₁ ε₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, rigSection_fst_assoc, Category.assoc, hε, ←
      Category.assoc, e₂,
      Category.assoc, rigSection_fst]
  · rw [Category.assoc, pullback.lift_snd, rigSection_snd_assoc, Category.assoc, rigSection_snd,
      Category.comp_id]

include hε in
/-- Transport rigidification through the two compatible pullback squares. -/
theorem rigSection_comp_eq_comp_pullbackMap_rigSection
    (d : pullback f t ⟶ pullback (pullback.fst f₁ g₁ ≫ f₁) ι) (v : T ⟶ pullback g₁ ι)
    (hd₁ : d ≫ pullback.fst _ _ = pullback.map f t f₁ g₁ a u ι e₁ e₂) (hd₂ : d ≫ pullback.snd _ _ =
      pullback.fst f t ≫ f)
    (hv₁ : v ≫ pullback.fst _ _ = u) (hv₂ : v ≫ pullback.snd _ _ = t)
    (e₃ : g₁ ≫ 𝟙 _ = rigSection f₁ g₁ ε₁ ≫ (pullback.fst f₁ g₁ ≫ f₁)) (e₄ : ι ≫ 𝟙 _ = 𝟙 _ ≫ ι) :
    rigSection f t ε ≫ d =
      v ≫ pullback.map g₁ ι (pullback.fst f₁ g₁ ≫ f₁) ι (rigSection f₁ g₁ ε₁) (𝟙 _) (𝟙 _) e₃ e₄
        := by
  apply pullback.hom_ext
  · rw [Category.assoc, hd₁, rigSection_comp_pullbackMap f t ε f₁ g₁ ε₁ ι a u e₁ e₂ hε,
      Category.assoc,
      pullback.lift_fst, ← Category.assoc, hv₁]
  · rw [Category.assoc, hd₂, rigSection_fst_comp, Category.assoc, pullback.lift_snd,
      Category.comp_id, hv₂]

end Sections

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages

section Modules

/-- Triviality of the pulled-back module is preserved by isomorphisms of the square. -/
theorem nonempty_pullback_pullback_iso_unit {U XR Q P : Scheme.{0}} (eU : U ≅ XR) (e : Q ≅ P)
    (r : U ⟶ Q) (sR : XR ⟶ P)
    (h : eU.hom ≫ sR = r ≫ e.hom) (N : Q.Modules)
    (hN : Nonempty ((Scheme.Modules.pullback r).obj N ≅ SheafOfModules.unit U.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback sR).obj ((Scheme.Modules.pullback e.inv).obj N) ≅
      SheafOfModules.unit XR.ringCatSheaf) := by
  have h' : sR ≫ e.inv = eU.inv ≫ r := by
    rw [← cancel_epi eU.hom, ← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id,
      eU.hom_inv_id_assoc]
  exact ⟨(Scheme.Modules.pullbackComp sR e.inv).app N ≪≫ (Scheme.Modules.pullbackCongr h').app N ≪≫
    ((Scheme.Modules.pullbackComp eU.inv r).app N).symm ≪≫ (Scheme.Modules.pullback eU.inv).mapIso
      hN.some ≪≫
    Scheme.Modules.pullbackUnitIso eU.inv⟩

/-- Transport a module comparison through an isomorphism of the source. -/
theorem nonempty_iso_pullback {X P P' : Scheme.{0}} (e : X ≅ P) (cX : P ⟶ P') (gA : X ⟶ P')
    (hgA : gA = e.hom ≫ cX) (M' : P'.Modules) (N : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback cX).obj M' ≅ (Scheme.Modules.pullback e.inv).obj N)) :
    Nonempty (N ≅ (Scheme.Modules.pullback gA).obj M') := by
  obtain ⟨e₁⟩ := h
  exact ⟨((Scheme.Modules.pullbackCongr hgA).app M' ≪≫ ((Scheme.Modules.pullbackComp e.hom cX).app
    M').symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso e₁ ≪≫ (Scheme.Modules.pullbackComp e.hom e.inv).app N ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).app N ≪≫ (Scheme.Modules.pullbackId X).app N).symm⟩

end Modules

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages

section Cube

variable {R R' : Type} [CommRing R] [CommRing R']
  {Aj : Scheme.{0}} (fj : Aj ⟶ Spec (CommRingCat.of R))
  {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of R'))
  (ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (a : A' ⟶ Aj) (ha : IsPullback a f' fj ι')

/-- The induced map between the two-fold fibre products. -/
abbrev sqMap : pullback f' f' ⟶ pullback fj fj := pullback.map f' f' fj fj a a ι' ha.w.symm
  ha.w.symm

/-- The square map commutes with the product structure map. -/
theorem sqMap_prodStr : prodStr f' f' ≫ ι' = sqMap fj f' ι' a ha ≫ prodStr fj fj := by
  have h1 : sqMap fj f' ι' a ha ≫ pullback.fst fj fj = pullback.fst f' f' ≫ a := pullback.lift_fst
    _ _ _
  change (pullback.fst f' f' ≫ f') ≫ ι' = sqMap fj f' ι' a ha ≫ pullback.fst fj fj ≫ fj
  rw [Category.assoc, ← Category.assoc (sqMap fj f' ι' a ha), h1, Category.assoc, ha.w]

/-- The square map defines the base change of the product. -/
theorem isPullback_sqMap : IsPullback (sqMap fj f' ι' a ha) (prodStr f' f') (prodStr fj fj) ι' :=
  AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback fj fj ι' f' f' a a
    ha ha

/-- The induced map between the three-fold fibre products. -/
abbrev cubeMap : pullback (prodStr f' f') f' ⟶ pullback (prodStr fj fj) fj :=
  pullback.map (prodStr f' f') f' (prodStr fj fj) fj (sqMap fj f' ι' a ha) a ι' (sqMap_prodStr fj
    f' ι' a ha) ha.w.symm

/-- The cube map defines the base change of the triple product. -/
theorem isPullback_cubeMap :
    IsPullback (cubeMap fj f' ι' a ha) (pullback.fst (prodStr f' f') f' ≫ prodStr f' f')
      (pullback.fst (prodStr fj fj) fj ≫ prodStr fj fj) ι' :=
  AlgebraicGeometry.isPullback_pullbackMap_fst_comp_of_isPullback_of_isPullback (prodStr fj fj) fj
    ι' (prodStr f' f') f'
    (sqMap fj f' ι' a ha) a (isPullback_sqMap fj f' ι' a ha) ha

end Cube

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages

section CubeUnit

variable {R R' : Type} [CommRing R] [CommRing R']
  {Aj : Scheme.{0}} (fj : Aj ⟶ Spec (CommRingCat.of R))
  {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
  (a : A' ⟶ Aj) (ha : IsPullback a f' fj (Spec.map (CommRingCat.ofHom φ)))

/-- The square map preserves the identity section of the product group. -/
theorem prod_one_coe_comp_sqMap (L' : RelativeGroupLaw R' f') (Lj : RelativeGroupLaw R fj)
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t f'),
      (L'.mul t P Q).1 ≫ a = (Lj.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R')) :
    ((L'.prod L').one t).1 ≫ sqMap fj f' (Spec.map (CommRingCat.ofHom φ)) a ha =
      ((Lj.prod Lj).one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have h1 : (L'.one t).1 ≫ a = (Lj.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 := one_comp_eq_one
    L' Lj φ a ha hLa t
  rw [RelativeGroupLaw.prod_one, RelativeGroupLaw.prod_one]
  change pullback.lift (L'.one t).1 (L'.one t).1 _ ≫ pullback.map f' f' fj fj a a _ _ _ =
    pullback.lift (Lj.one (t ≫ Spec.map (CommRingCat.ofHom φ))).1 (Lj.one (t ≫ Spec.map
      (CommRingCat.ofHom φ))).1 _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, h1]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd, h1]

end CubeUnit

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages

end CubeDescentAux

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages
open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux

end

open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages
open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux

open _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux

end JacobianVarieties.Picard.Proofs.FGProductModel

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard
open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux.FGStages
open scoped _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux
open _root_.JacobianVarieties.Picard.Proofs.FGProductModel.CubeDescentAux

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

open _root_.AlgebraicGeometry.Scheme.Modules in
/-- Descend the rigidified product bundle and group law to a finitely generated subalgebra. -/
theorem exists_fg_subalgebra_isPullback_prodStr_model
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f) :
    ∃ (S₁ : Subalgebra ℤ S) (_ : S₁.FG)
      (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁)
      (_ : L₁.IsCommutative) (_ : AbelianSchemePropertyBundle ↥S₁ f₁)
      (a : A ⟶ A₁) (ha : IsPullback a f f₁ (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)))
      (_ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ a = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
      (M₁ : RigidifiedLineBundle (prodStr f₁ f₁) ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of ↥S₁))))
        f₁),
      Nonempty (M.L ≅ (Scheme.Modules.pullback
        (pullback.map (prodStr f f) f (prodStr f₁ f₁) f₁
          (pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm
            ha.w.symm)
          a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
          (by
            have h1 : pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom))
              ha.w.symm ha.w.symm ≫
                pullback.fst f₁ f₁ = pullback.fst f f ≫ a := pullback.lift_fst _ _ _
            change (pullback.fst f f ≫ f) ≫ Spec.map (CommRingCat.ofHom S₁.val.toRingHom) =
              pullback.map f f f₁ f₁ a a (Spec.map (CommRingCat.ofHom S₁.val.toRingHom)) ha.w.symm
                ha.w.symm ≫
                pullback.fst f₁ f₁ ≫ f₁
            rw [Category.assoc, ← Category.assoc (pullback.map _ _ _ _ _ _ _ _ _), h1,
              Category.assoc, ha.w])
          ha.w.symm)).obj M₁.L) := by
  classical
  obtain ⟨T, hT, -, A₁, f₁, L₁, a₁, ha₁, hA₁, -, -, hLa₁⟩ :=
    L.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
      (A₀ := ℤ) hA ∅
  have := hA₁.proper
  have : Nonempty (FGStages.Idx T) := FGStages.nonempty T hT
  have hLa₁' : ∀ (T' : Scheme.{0}) (t : T' ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁,
          by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1 := fun T' t P Q => hLa₁ t P Q
  have hqc : QuasiCompact (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) := inferInstance
  have hqs : QuasiSeparated (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) := inferInstance
  have hs₁ : rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 _)) ≫ (pullback.fst (prodStr f₁ f₁)
    f₁ ≫ prodStr f₁ f₁) = f₁ :=
    rigSection_fst_comp _ _ _
  have hε₁ : ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ sqMap f₁ f (Spec.map
    (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁ =
      Spec.map (CommRingCat.ofHom (algebraMap ↥T S)) ≫ ((L₁.prod L₁).one (𝟙 (Spec (CommRingCat.of
        ↥T)))).1 := by
    rw [prod_one_coe_comp_sqMap f₁ f _ a₁ ha₁ L L₁ hLa₁', one_coe_eq_comp_one (L₁.prod L₁),
      Category.id_comp]
  have hc₁ := isPullback_cubeMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁
  have h𝓛 := M.isInvertible.pullback hc₁.isoPullback.inv
  have hsq₁ : ha₁.isoPullback.hom ≫ pullback.map f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
        (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) (Spec.map (CommRingCat.ofHom (algebraMap
          ↥T S)))
        (rigSection (prodStr f₁ f₁) f₁ ((L₁.prod L₁).one (𝟙 _))) (𝟙 _) (𝟙 _)
        (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) =
      rigSection (prodStr f f) f ((L.prod L).one (𝟙 _)) ≫ hc₁.isoPullback.hom :=
    (rigSection_comp_eq_comp_pullbackMap_rigSection (prodStr f f) f ((L.prod L).one (𝟙 _)) (prodStr
      f₁ f₁) f₁
      ((L₁.prod L₁).one (𝟙 _)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T S)))
      (sqMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁) a₁
      (sqMap_prodStr f₁ f _ a₁ ha₁) ha₁.w.symm hε₁
      hc₁.isoPullback.hom ha₁.isoPullback.hom (IsPullback.isoPullback_hom_fst _)
        (IsPullback.isoPullback_hom_snd _)
      (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])).symm
  have htriv := nonempty_pullback_pullback_iso_unit ha₁.isoPullback hc₁.isoPullback _ _ hsq₁ _
    M.rigidified
  obtain ⟨k, hik, 𝓛k, h𝓛k, ⟨erig⟩, hcmp⟩ :=
    exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
      (FGStages.φ T) (FGStages.g T) (FGStages.isDirectLimit T hT) (⟨T, hT, le_rfl⟩ : FGStages.Idx T)
      (pullback.fst (prodStr f₁ f₁) f₁ ≫ prodStr f₁ f₁) f₁ (rigSection (prodStr f₁ f₁) f₁ ((L₁.prod
        L₁).one (𝟙 _))) hs₁ _ h𝓛 htriv
  obtain ⟨A₂, f₂, L₂, hA₂, a₂, ha₂, b, hb, hab, hLa₂, hLb⟩ :=
    L.exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
      (algebraMap ↥T S) (FGStages.g T k) (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik)
      (FGStages.g_comp_φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik) A₁ f₁ L₁ hA₁ a₁ ha₁ hLa₁'
  have hc₂ := isPullback_cubeMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩
    : FGStages.Idx T) k hik))) b hb
  have hε₂ : ((L₂.prod L₂).one (𝟙 _)).1 ≫ sqMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T
    (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik))) b hb =
      Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k hik)) ≫
        ((L₁.prod L₁).one (𝟙 _)).1 := by
    rw [prod_one_coe_comp_sqMap f₁ f₂ _ b hb L₂ L₁ hLb, one_coe_eq_comp_one (L₁.prod L₁),
      Category.id_comp]
  have hsq₂ := rigSection_comp_eq_comp_pullbackMap_rigSection (prodStr f₂ f₂) f₂ ((L₂.prod L₂).one
    (𝟙 _)) (prodStr f₁ f₁) f₁
      ((L₁.prod L₁).one (𝟙 _)) (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ :
        FGStages.Idx T) k hik)))
      (sqMap f₁ f₂ _ b hb) b (sqMap_prodStr f₁ f₂ _ b hb) hb.w.symm hε₂
      hc₂.isoPullback.hom hb.isoPullback.hom (IsPullback.isoPullback_hom_fst _)
        (IsPullback.isoPullback_hom_snd _)
      (IsPullback.isoPullback_hom_fst _) (IsPullback.isoPullback_hom_snd _)
      (by rw [hs₁, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  refine ⟨k.1, k.2.1, A₂, f₂, L₂, GoodReductionJacobian.AbelianSchemePropertyBundle.isCommutative
    hA₂ L₂, hA₂, a₂, ha₂, hLa₂,
    { L := (Scheme.Modules.pullback hc₂.isoPullback.hom).obj 𝓛k
      isInvertible := h𝓛k.pullback _
      rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app 𝓛k ≪≫ (Scheme.Modules.pullbackCongr
        hsq₂).app 𝓛k ≪≫
        ((Scheme.Modules.pullbackComp _ _).app 𝓛k).symm ≪≫ (Scheme.Modules.pullback
          hb.isoPullback.hom).mapIso erig ≪≫
        Scheme.Modules.pullbackUnitIso _⟩ }, ?_⟩
  have hsq : sqMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫
      sqMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k
        hik))) b hb =
      sqMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hab]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hab]
  have hmap : cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫
      cubeMap f₁ f₂ (Spec.map (CommRingCat.ofHom (FGStages.φ T (⟨T, hT, le_rfl⟩ : FGStages.Idx T) k
        hik))) b hb =
      cubeMap f₁ f (Spec.map (CommRingCat.ofHom (algebraMap ↥T S))) a₁ ha₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hsq]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hab]
  have h₁ : (hc₁.isoPullback.inv ≫ cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂
    ha₂ ≫ hc₂.isoPullback.hom) ≫
      pullback.fst _ _ = pullback.fst _ _ := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst, hmap]
    rw [Iso.inv_comp_eq]
    exact hc₁.isoPullback_hom_fst.symm
  have h₂ : (hc₁.isoPullback.inv ≫ cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂
    ha₂ ≫ hc₂.isoPullback.hom) ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (FGStages.g T k)) := by
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_fst_assoc,
      ← sqMap_prodStr f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂]
    rw [Iso.inv_comp_eq, hc₁.isoPullback_hom_snd_assoc, Category.assoc]
    rfl
  have key := nonempty_iso_pullback hc₁.isoPullback
    (hc₁.isoPullback.inv ≫ cubeMap f₂ f (Spec.map (CommRingCat.ofHom (FGStages.g T k))) a₂ ha₂ ≫
      hc₂.isoPullback.hom) _
    (Iso.hom_inv_id_assoc _ _).symm 𝓛k _ (hcmp _ h₁ h₂)
  exact ⟨key.some ≪≫ ((Scheme.Modules.pullbackComp _ _).app 𝓛k).symm⟩
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

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

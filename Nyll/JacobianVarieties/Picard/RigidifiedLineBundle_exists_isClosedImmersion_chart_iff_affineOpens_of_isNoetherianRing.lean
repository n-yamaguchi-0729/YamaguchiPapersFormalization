/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.Choose
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_bijective_specIso_inv_comp_appTop_of_isPullback
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover

/-!
Noetherian affine charts representing triviality of a rigidified line bundle.
The construction compares local triviality with the proper flat representability theorem.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NoetherianChart
attribute [-instance]
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
attribute [-instance]
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
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
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
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
attribute [-simp]
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans
  AlgebraicGeometry.SubalgebraStages.cone_pt
attribute [-simp]
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
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst_assoc
attribute [-simp]
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd_assoc
  GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation

namespace DockHelpers

/-- The base-change projection induces a bijection on global sections. -/
theorem hH0 {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (B : Type) [CommRing B] [Algebra R B] :
    Function.Bijective (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R
      B)))).appTop := by
  have hb := hA.bijective_specIso_inv_comp_appTop_of_isPullback
    (algebraMap R B) (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R B))))
      (IsPullback.of_hasPullback _ _)
  have hi : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ hi).mp hb

section Geometry

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
  {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
  (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
  (U : X.Opens)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ (U : Scheme.{0})) (hψ : (ψU ≫ U.ι) ≫
    g = t)

/-- The comparison from an iterated pullback to the pullback at the given point. -/
noncomputable def α : Limits.pullback (Limits.pullback.snd f (U.ι ≫ g)) ψU ⟶ Limits.pullback f t :=
  Limits.pullback.lift
    (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫ Limits.pullback.fst f (U.ι ≫ g))
    (Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU)
    (by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Limits.pullback.condition,
        Category.assoc, ← hψ,
          Category.assoc])

/-- The comparison respects the map to the original family. -/
theorem α_comp_baseChangeSnd :
    α g U t ψU hψ ≫ baseChangeSnd f (⟨ψU ≫ U.ι, hψ⟩ : SchemeHomOver t g) =
      Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫ baseChangeSnd f (⟨U.ι, rfl⟩ :
        SchemeHomOver (U.ι ≫ g) g) := by
  unfold α baseChangeSnd
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
      Limits.pullback.condition_assoc]

include hψ in
/-- A trivial bundle at a point gives a trivial bundle on the iterated pullback. -/
theorem iso_of_trivial
    (e : (M.pullbackAlong (⟨ψU ≫ U.ι, hψ⟩ : SchemeHomOver t g)).L ≅
      (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) :
    Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g))
      ψU)).obj
        ((Scheme.Modules.pullback (baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g))).obj
          M.L) ≅
      (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
        (SheafOfModules.unit (Limits.pullback f (U.ι ≫ g)).ringCatSheaf)) :=
  ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (α_comp_baseChangeSnd g U t ψU hψ).symm).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    (Scheme.Modules.pullback (α g U t ψU hψ)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (α g U t ψU hψ) ≪≫
    (Scheme.Modules.pullbackUnitIso _).symm⟩

include hψ in
/-- The comparison from a further base change to the iterated pullback. -/
noncomputable def δ {T' : Scheme.{0}} (v : T' ⟶ T) :
    Limits.pullback f (v ≫ t) ⟶ Limits.pullback (Limits.pullback.snd f (U.ι ≫ g)) ψU :=
  Limits.pullback.lift
    (Limits.pullback.lift (Limits.pullback.fst f (v ≫ t)) (Limits.pullback.snd f (v ≫ t) ≫ v ≫ ψU)
      (by rw [Limits.pullback.condition, ← hψ]; simp only [Category.assoc]))
    (Limits.pullback.snd f (v ≫ t) ≫ v)
    (by rw [Limits.pullback.lift_snd, Category.assoc])

/-- The further base-change comparison respects the original family map. -/
theorem δ_comp {T' : Scheme.{0}} (v : T' ⟶ T) (hv : (v ≫ ψU ≫ U.ι) ≫ g = v ≫ t) :
    δ g U t ψU hψ v ≫ Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫
        baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g) =
      baseChangeSnd f (⟨v ≫ ψU ≫ U.ι, hv⟩ : SchemeHomOver (v ≫ t) g) := by
  unfold δ baseChangeSnd
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
      Category.comp_id]
  · simp only [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
      Limits.pullback.lift_fst_assoc]

/-- The second projection of the further base-change comparison. -/
theorem δ_comp_snd {T' : Scheme.{0}} (v : T' ⟶ T) :
    δ g U t ψU hψ v ≫ Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU =
      Limits.pullback.snd f (v ≫ t) ≫ v := by
  unfold δ
  rw [Limits.pullback.lift_snd]

include hψ in
/-- An isomorphism on a restricted iterated pullback gives triviality on that open. -/
theorem trivial_of_iso_on (V : T.Opens)
    (e : (Scheme.Modules.pullback ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ
      V).ι).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
          ((Scheme.Modules.pullback (baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g))).obj
            M.L)) ≅
      (Scheme.Modules.pullback ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ
        V).ι).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU)).obj
          (SheafOfModules.unit (Limits.pullback f (U.ι ≫ g)).ringCatSheaf)))
    (hv : (V.ι ≫ ψU ≫ U.ι) ≫ g = V.ι ≫ t) :
    Nonempty ((M.pullbackAlong (⟨V.ι ≫ ψU ≫ U.ι, hv⟩ : SchemeHomOver (V.ι ≫ t) g)).L ≅
      (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) (V.ι ≫ t)).L)
        := by
  have hr : Set.range (δ g U t ψU hψ V.ι) ⊆
      Set.range ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change (Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) (δ g U t ψU hψ V.ι w) ∈ V
    rw [← Scheme.Hom.comp_apply, δ_comp_snd, Scheme.Hom.comp_apply]
    exact (Limits.pullback.snd f (V.ι ≫ t) w).2
  let γ := IsOpenImmersion.lift ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι
    (δ g U t ψU hψ V.ι) hr
  have hγ : γ ≫ ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι = δ g U t ψU
    hψ V.ι :=
    IsOpenImmersion.lift_fac _ _ hr
  have hcomp : baseChangeSnd f (⟨V.ι ≫ ψU ≫ U.ι, hv⟩ : SchemeHomOver (V.ι ≫ t) g) =
      (γ ≫ ((Limits.pullback.snd (Limits.pullback.snd f (U.ι ≫ g)) ψU) ⁻¹ᵁ V).ι) ≫
        (Limits.pullback.fst (Limits.pullback.snd f (U.ι ≫ g)) ψU ≫
          baseChangeSnd f (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g) g)) := by
    rw [hγ, δ_comp]
  exact ⟨(Scheme.Modules.pullbackCongr hcomp).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp _ _).app M.L).symm ≪≫
    ((Scheme.Modules.pullbackComp γ _).app _).symm ≪≫
    (Scheme.Modules.pullback γ).mapIso e ≪≫
    (Scheme.Modules.pullbackComp γ _).app _ ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    Scheme.Modules.pullbackUnitIso _⟩

end Geometry

end DockHelpers

end JacobianVarieties.Picard.Proofs.NoetherianChart

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open _root_.JacobianVarieties.Picard.Proofs.NoetherianChart in
open AlgebraicGeometry.Scheme.Modules.IsInvertible in
/-- The triviality locus has a representing closed immersion on every affine open. -/
theorem
exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
    {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens) :
    ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})), IsClosedImmersion ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU) := by
  have : IsProper f := hA.proper
  have : Smooth f := hA.smooth
  have : GeometricallyIntegral f :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing hA
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨Z, ι, hι, hZ⟩ :=
    exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
      f (DockHelpers.hH0 hA) ((U : X.Opens).ι ≫ g)
      ((Scheme.Modules.pullback (baseChangeSnd f (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U :
        X.Opens).ι ≫ g) g))).obj M.L)
      (SheafOfModules.unit (Limits.pullback f ((U : X.Opens).ι ≫ g)).ringCatSheaf)
      (M.isInvertible.pullback _) (Scheme.Modules.isInvertible_unit _)
  refine ⟨Z, ι, hι, ?_⟩
  intro T t ψU hψ
  refine Iff.trans ?_ (hZ ψU).symm
  constructor
  · rintro ⟨e⟩
    obtain ⟨e'⟩ := DockHelpers.iso_of_trivial L g M (U : X.Opens) t ψU hψ e
    exact Scheme.Modules.LocallyIsoOver.of_iso _ e'
  · intro hloc
    choose V hVmem hViso using hloc
    let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers (↥T) (fun τ => ((V τ : T.Opens) : Scheme.{0}))
      (fun τ => (V τ).ι)
      (fun x => ⟨x, ⟨x, hVmem x⟩, rfl⟩)
    refine (nonempty_iso_unit_iff_forall_openCover L hA g M t
      (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g) 𝒰).mpr fun τ => ?_
    obtain ⟨e⟩ := hViso τ
    exact DockHelpers.trivial_of_iso_on L g M (U : X.Opens) t ψU hψ (V τ) e _
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

attribute [-simp]
  GoodReductionJacobian.RelativeGroupLaw.sndPoint_coe
  GoodReductionJacobian.RelativeGroupLaw.fstPoint_coe
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
attribute [-simp]
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
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst
attribute [-simp]
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst_assoc
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd_assoc
  GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst

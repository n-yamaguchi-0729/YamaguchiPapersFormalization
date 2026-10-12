/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Monoidal.Category
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesPullbackMonoidalV2
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_LocIsoOnBase_equivalence
import Nyll.AlgebraicCurves.Geometry.Picard.Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_of_isPullback
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_prodStr_commRing
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Product

/-!
# Triviality of a rigidified bundle on the identity face

Use the naturality of the group identity to compare the identity face with base
change. Local triviality on the face and the sections of the proper abelian
scheme yield a global trivialization compatible with the rigidification.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.UnitOneFace
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
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AdicCompletion.instIsLocalRingMaximalIdeal
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
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry.RelPicard


with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem nonempty_pullbackAlong_one_iso_unit_of_locIsoOnBase_face
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)
    (h₃ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift (𝟙 _) (L.one (prodStr f f)).1
          (by rw [Category.id_comp, (L.one _).2]))).obj M.L) (𝟙_ _)) :
    Nonempty ((M.pullbackAlong (L.one (𝟙 (Spec (CommRingCat.of S))))).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f)
        (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S))))
        (𝟙 _)).L) := by
  classical
  let c := prodStr f f
  let e : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f := L.one (𝟙 (Spec (CommRingCat.of S)))
  let face : pullback f f ⟶ pullback c f :=
    pullback.lift (𝟙 _) (L.one (prodStr f f)).1 (by rw [Category.id_comp, (L.one _).2])
  have hone : (L.one (prodStr f f)).1 = prodStr f f ≫ e.1 := by
    have := L.one_natural (𝟙 (Spec (CommRingCat.of S)))
      (prodStr f f) (prodStr f f) (Category.comp_id _)
    rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]
  have hbc : baseChangeSnd c e = pullback.fst c (𝟙 _) ≫ face := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      unfold baseChangeSnd
      rw [pullback.map]
      erw [pullback.lift_fst]
      rw [Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, hone, ← Category.assoc, pullback.condition,
        Category.assoc]
      unfold baseChangeSnd
      erw [pullback.lift_snd]
      rfl
  have h₃' := LocIsoOnBase.pullback_of_comp_eq (g := c)
    (pullback.snd c (𝟙 _)) (pullback.fst c (𝟙 _)) (𝟙 _)
    pullback.condition h₃
  have eM : (Scheme.Modules.pullback (pullback.fst c (𝟙 _))).obj
      ((Scheme.Modules.pullback face).obj M.L) ≅
      (M.pullbackAlong e).L :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hbc.symm).app M.L
  have eU : (Scheme.Modules.pullback (pullback.fst c (𝟙 _))).obj (𝟙_ (pullback f f).Modules) ≅
      (RigidifiedLineBundle.unit (c := prodStr f f)
        (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S))))
        (𝟙 _)).L :=
    Scheme.Modules.pullbackTensorUnitObjIso _
  have equivB := LocIsoOnBase.equivalence (pullback.snd c (𝟙 (Spec (CommRingCat.of S))))
  have hloc : LocIsoOnBase (pullback.snd c (𝟙 _)) (M.pullbackAlong e).L
      (RigidifiedLineBundle.unit (c := prodStr f f)
        (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S))))
        (𝟙 _)).L :=
    equivB.trans (equivB.trans
      (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso eM.symm⟩⟩) h₃')
      (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso eU⟩⟩)
  have hP : AbelianSchemePropertyBundle S c := hA.prodStr_commRing hA
  have hB : AbelianSchemePropertyBundle S (pullback.snd c (𝟙 (Spec (CommRingCat.of S)))) :=
    hP.of_isPullback (IsPullback.of_hasPullback c (𝟙 _))
  have : IsProper (pullback.snd c (𝟙 (Spec (CommRingCat.of S)))) := hB.proper
  have hH0 := hB.bijective_algebraMap_sections_pullback
  exact nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
    (pullback.snd c (𝟙 _)) hH0 (rigSection c (𝟙 _) ((L.prod L).one (𝟙 _))) (pullback.lift_snd _ _ _)
    _ _ (M.pullbackAlong e).isInvertible (RigidifiedLineBundle.unit _).isInvertible hloc
    (M.pullbackAlong e).rigidified.some (RigidifiedLineBundle.unit (𝟙 _)).rigidified.some
end JacobianVarieties.Picard.Proofs.UnitOneFace
end ProofImplementation

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
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
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
  IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of
  IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
attribute [-simp]
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
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst

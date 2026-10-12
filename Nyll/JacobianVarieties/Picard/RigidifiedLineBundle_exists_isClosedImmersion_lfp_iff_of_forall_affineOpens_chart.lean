/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_iff_of_forall_affineOpens_chart.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart

/-! Local finite-presentation criteria for the triviality locus of a rigidified line bundle. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.LfpChartCriterion
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
attribute [-simp]
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
end JacobianVarieties.Picard.Proofs.LfpChartCriterion

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

open _root_.JacobianVarieties.Picard.Proofs.LfpChartCriterion
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation

/-- Local finite-presentation criteria for the triviality locus of a rigidified line bundle. -/
theorem exists_isClosedImmersion_lfp_iff_of_forall_affineOpens_chart
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
    (hloc : ∀ U : X.affineOpens, ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})),
        IsClosedImmersion ιU ∧ LocallyOfFinitePresentation ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU)) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g),
        Nonempty ((M.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z, ψ₀ ≫ ι = ψ.1 := by
  obtain ⟨Z, ι, hι, hZ⟩ :=
    exists_isClosedImmersion_iff_of_forall_affineOpens_chart L hA g M
      (fun U => by
        obtain ⟨ZU, ιU, hcl, -, hZU⟩ := hloc U
        exact ⟨ZU, ιU, hcl, hZU⟩)
  refine ⟨Z, ι, hι, ?_, hZ⟩
  have : IsClosedImmersion ι := hι
  have : IsZariskiLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{0})
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFinitePresentation)
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X)
  intro U
  obtain ⟨ZU, ιU, hcl, hlfp, hZU⟩ := hloc U
  have : IsClosedImmersion ιU := hcl
  have : LocallyOfFinitePresentation ιU := hlfp
  have htrivZ : Nonempty ((M.pullbackAlong (⟨(ι ∣_ U) ≫ (U : X.Opens).ι, rfl⟩ :
      SchemeHomOver (((ι ∣_ U) ≫ (U : X.Opens).ι) ≫ g) g)).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) (((ι ∣_ U) ≫
          (U : X.Opens).ι) ≫ g)).L) :=
    (hZ (((ι ∣_ U) ≫ (U : X.Opens).ι) ≫ g) ⟨(ι ∣_ U) ≫ (U : X.Opens).ι, rfl⟩).mpr
      ⟨(ι ⁻¹ᵁ (U : X.Opens)).ι, (morphismRestrict_ι ι U).symm⟩
  obtain ⟨k, hk⟩ := (hZU (((ι ∣_ U) ≫ (U : X.Opens).ι) ≫ g) (ι ∣_ U) rfl).mp htrivZ
  have htrivU : Nonempty ((M.pullbackAlong (⟨ιU ≫ (U : X.Opens).ι, rfl⟩ :
      SchemeHomOver ((ιU ≫ (U : X.Opens).ι) ≫ g) g)).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) ((ιU ≫ (U :
          X.Opens).ι) ≫ g)).L) :=
    (hZU ((ιU ≫ (U : X.Opens).ι) ≫ g) ιU rfl).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨n, hn⟩ := (hZ ((ιU ≫ (U : X.Opens).ι) ≫ g) ⟨ιU ≫ (U : X.Opens).ι, rfl⟩).mp htrivU
  have hP := isPullback_morphismRestrict ι (U : X.Opens)
  let m : ZU ⟶ ↑(ι ⁻¹ᵁ (U : X.Opens)) := hP.lift ιU n hn.symm
  have hm : m ≫ (ι ∣_ U) = ιU := hP.lift_fst _ _ _
  have hmk : m ≫ k = 𝟙 _ := by
    rw [← cancel_mono ιU, Category.assoc, hk, hm, Category.id_comp]
  have hkm : k ≫ m = 𝟙 _ := by
    rw [← cancel_mono (ι ∣_ U), Category.assoc, hm, hk, Category.id_comp]
  have : IsIso k := ⟨⟨m, hkm, hmk⟩⟩
  rw [← hk]
  infer_instance
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Adjoin.FG
import Nyll.SchemeTheory.Descent.SubalgebraStages
import Nyll.SchemeTheory.Descent.SubalgebraStages_nonempty_isLimit_cone

/-!
# exists fg subalgebra hom pullback of hom pullback of locally Of Finite Presentation
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

end exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open AlgebraicCurves.Geometry.Schemes.Proofs
  exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation

universe u

open _root_.AlgebraicGeometry.SubalgebraStages

theorem exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
        ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
          q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)
            →
          q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
          q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom)
            →
          q₁ ≫ g₀ = g ≫ q₂ := by
  classical
  let ι : Type u := {T : Subalgebra A₀ A // T.FG ∧ (↑s : Set A) ⊆ T}
  have : Nonempty ι := ⟨⟨Algebra.adjoin A₀ ↑s, Subalgebra.fg_adjoin_finset s,
    Algebra.subset_adjoin⟩⟩
  have : IsDirected ι (· ≤ ·) := ⟨fun T₁ T₂ =>
    ⟨⟨T₁.1 ⊔ T₂.1, T₁.2.1.sup T₂.2.1, T₁.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
      (le_sup_left : T₁.1 ≤ T₁.1 ⊔ T₂.1), (le_sup_right : T₂.1 ≤ T₁.1 ⊔ T₂.1)⟩⟩
  let S : ι →o Subalgebra A₀ A := ⟨fun T => T.1, fun _ _ h => h⟩
  have hS : ∀ x : A, ∃ i, x ∈ S i := fun x =>
    ⟨⟨Algebra.adjoin A₀ ↑(insert x s), Subalgebra.fg_adjoin_finset _,
        fun y hy => Algebra.subset_adjoin (by simp [hy])⟩,
      Algebra.subset_adjoin (by simp)⟩
  obtain ⟨hc⟩ := SubalgebraStages.nonempty_isLimit_cone S hS f₁
  let t : diagram S f₁ ⟶ (Functor.const ιᵒᵖ).obj (Spec (CommRingCat.of A₀)) :=
    { app := fun i => pullback.fst f₁ (specHom S i.unop) ≫ f₁
      naturality := fun i j h => by
        erw [Category.comp_id]
        exact diagram_map_fst_assoc S f₁ h f₁ }
  have hg₀ : g ≫ pullback.snd f₂ (specHomTop (A₀ := A₀) (A := A)) = pullback.snd f₁ (specHomTop (A₀
    := A₀) (A := A)) := hg
  have e₁ : pullback.fst f₁ (specHomTop (A₀ := A₀) (A := A)) ≫ f₁ = pullback.snd f₁ (specHomTop (A₀
    := A₀) (A := A)) ≫ (specHomTop (A₀ := A₀) (A := A)) := pullback.condition
  have e₂ : pullback.fst f₂ (specHomTop (A₀ := A₀) (A := A)) ≫ f₂ = pullback.snd f₂ (specHomTop (A₀
    := A₀) (A := A)) ≫ (specHomTop (A₀ := A₀) (A := A)) := pullback.condition
  let a : (cone S f₁).pt ⟶ X₂ := g ≫ pullback.fst f₂ (specHomTop (A₀ := A₀) (A := A))
  have ha' : ∀ i : ιᵒᵖ, (cone S f₁).π.app i ≫ t.app i = a ≫ f₂ := fun i => by
    change (cone S f₁).π.app i ≫ pullback.fst f₁ (specHom S i.unop) ≫ f₁ = (g ≫ pullback.fst f₂
      (specHomTop (A₀ := A₀) (A := A))) ≫ f₂
    refine (cone_π_app_fst_assoc S f₁ i f₁).trans ?_
    refine e₁.trans ?_
    rw [← hg₀, Category.assoc, Category.assoc]
    exact congrArg (g ≫ ·) e₂.symm
  have ha : (cone S f₁).π ≫ t = (Functor.const ιᵒᵖ).map (a ≫ f₂) := by
    ext i
    exact ha' i
  obtain ⟨i, g', h1, h2⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (diagram S f₁) t f₂ (cone S f₁) hc a
      ha
  have h2' : g' ≫ f₂ = pullback.snd f₁ (specHom S i.unop) ≫ specHom S i.unop :=
    h2.trans pullback.condition
  refine ⟨S i.unop, i.unop.2.1, i.unop.2.2, pullback.lift g' (pullback.snd f₁ (specHom S i.unop))
    h2',
    pullback.lift_snd _ _ _, ?_⟩
  intro q₁ q₂ hq₁ hq₁' hq₂ hq₂'
  have hq : q₁ = (cone S f₁).π.app i := by
    apply pullback.hom_ext
    · exact hq₁.trans (cone_π_app_fst S f₁ i).symm
    · exact hq₁'.trans (cone_π_app_snd S f₁ i).symm
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hq]
    exact h1.trans (((congrArg (g ≫ ·) hq₂).symm).trans (Category.assoc _ _ _).symm)
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, hq₂', ← Category.assoc, hg]
    exact hq₁'
end AlgebraicGeometry
end ProofImplementation

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans

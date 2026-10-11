/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Adjoin.FG
import SchemeTheory.Descent.SubalgebraStages
import SchemeTheory.Descent.SubalgebraStages_nonempty_isLimit_cone

/-!
# exists fg subalgebra pullback fst comp eq of locally Of Finite Type
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

open _root_.AlgebraicGeometry.SubalgebraStages in
theorem _root_.AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [LocallyOfFiniteType f₂]
    (a b : X₁ ⟶ X₂) (ha : a ≫ f₂ = f₁) (hb : b ≫ f₂ = f₁)
    (hab : pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ a =
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ b) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ a =
        pullback.fst f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ b := by
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
  let i₀ : ιᵒᵖ := op (Classical.arbitrary ι)
  let t : diagram S f₁ ⟶ (Functor.const ιᵒᵖ).obj (Spec (CommRingCat.of A₀)) :=
    { app := fun i => pullback.fst f₁ (specHom S i.unop) ≫ f₁
      naturality := fun i j h => by
        erw [Category.comp_id]
        exact diagram_map_fst_assoc S f₁ h f₁ }
  obtain ⟨k, hki, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType (diagram S f₁) t f₂
    (cone S f₁) hc
    (i := i₀) (pullback.fst f₁ (specHom S i₀.unop) ≫ a) (pullback.fst f₁ (specHom S i₀.unop) ≫ b)
    (by rw [Category.assoc, ha]; try rfl) (by rw [Category.assoc, hb]; try rfl)
    (by rw [cone_π_app_fst_assoc S f₁ i₀, cone_π_app_fst_assoc S f₁ i₀]; exact hab)
  refine ⟨S k.unop, k.unop.2.1, k.unop.2.2, ?_⟩
  rw [diagram_map_fst_assoc S f₁ hki, diagram_map_fst_assoc S f₁ hki] at hk
  exact hk
end exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
end AlgebraicCurves.Geometry.Schemes.Proofs
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

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Iso

/-!
# Independence of inverse mates from the choice of left adjoints

For a fixed square of right adjoints, changing the chosen left adjoints
conjugates the inverse mate by the canonical comparison isomorphisms.
Consequently, invertibility of the inverse mate is independent of these choices.
This permits comparison of directly constructed stalk adjunctions with
composites of inverse-image and stalk adjunctions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace EtaleCohomology.Sites

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D}
  {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁) (adj₂' : L₂' ⊣ R₂)

private lemma inverseMate_change_leftAdjoints (β : TwoSquare R₁ H G R₂) :
    (mateEquiv adj₁' adj₂').symm β =
      (((mateEquiv adj₁ adj₂).symm β).whiskerLeft
        ((conjugateEquiv adj₁' adj₁).symm (𝟙 R₁))).whiskerRight
          ((conjugateEquiv adj₂ adj₂').symm (𝟙 R₂)) := by
  apply (mateEquiv adj₁' adj₂').injective
  rw [Equiv.apply_symm_apply, mateEquiv_conjugateEquiv_vcomp,
    conjugateEquiv_mateEquiv_vcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  apply TwoSquare.ext
  intro b
  change β.natTrans.app b =
    (G.map (𝟙 (R₁.obj b)) ≫ β.natTrans.app b) ≫ 𝟙 (R₂.obj (H.obj b))
  rw [Functor.map_id, Category.id_comp]
  exact (Category.comp_id (β.natTrans.app b)).symm

/-- Invertibility of the inverse mate of a fixed right square is unchanged
when its two left adjoints are replaced by other adjoints to the same functors. -/
lemma isIso_inverseMate_iff (β : TwoSquare R₁ H G R₂) :
    IsIso (((mateEquiv adj₁ adj₂).symm β).natTrans) ↔
      IsIso (((mateEquiv adj₁' adj₂').symm β).natTrans) := by
  rw [inverseMate_change_leftAdjoints adj₁ adj₂ adj₁' adj₂' β]
  change IsIso (((mateEquiv adj₁ adj₂).symm β).natTrans) ↔
    IsIso (Functor.whiskerLeft G ((conjugateEquiv adj₂ adj₂').symm (𝟙 R₂)) ≫
      (((mateEquiv adj₁ adj₂).symm β).natTrans ≫
        Functor.whiskerRight ((conjugateEquiv adj₁' adj₁).symm (𝟙 R₁)) H))
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

end EtaleCohomology.Sites

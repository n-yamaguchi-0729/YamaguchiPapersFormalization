/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Gluing a section in the local image of an injective sheaf morphism

This is the single-section version of the gluing argument in
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso'`, from
`Mathlib/CategoryTheory/Sites/LocallyBijective.lean` by Joël Riou.
Only the image sieve of the specified section needs to cover.
-/

noncomputable section

open CategoryTheory Opposite

namespace EtaleCohomology.Sites

universe u v w

/-- A section locally in the image of an objectwise injective sheaf morphism
has a global preimage. -/
theorem exists_section_lift_of_imageSieve_mem
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type w)} (η : F ⟶ G)
    (hη : ∀ U : Cᵒᵖ, Function.Injective (η.hom.app U))
    {U : C} (s : G.obj.obj (op U))
    (hs : Presheaf.imageSieve η.hom s ∈ J U) :
    ∃ a : F.obj.obj (op U), η.hom.app (op U) a = s := by
  have H := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property _ hs
  let a : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve η.hom s).arrows :=
    fun _ g hg => Presheaf.localPreimage η.hom s g hg
  have ha : a.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ h
    apply hη
    refine (NatTrans.naturality_apply η.hom g₁.op (a f₁ hf₁)).trans ?_
    refine (congrArg (G.obj.map g₁.op) (Presheaf.app_localPreimage η.hom s f₁ hf₁)).trans ?_
    refine Eq.trans ?_ ((congrArg (G.obj.map g₂.op)
      (Presheaf.app_localPreimage η.hom s f₂ hf₂)).symm.trans
        (NatTrans.naturality_apply η.hom g₂.op (a f₂ hf₂)).symm)
    rw [← G.obj.map_comp_apply, ← G.obj.map_comp_apply, ← op_comp, ← op_comp, h]
  refine ⟨H.amalgamate a ha, ?_⟩
  apply (((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated _ hs).ext
  intro V g hg
  rw [← NatTrans.naturality_apply, H.valid_glue ha]
  exact Presheaf.app_localPreimage η.hom s g hg

end EtaleCohomology.Sites

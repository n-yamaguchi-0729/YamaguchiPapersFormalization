/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.NatIso

/-!
# Fully faithful adjoints on sheaves

For an adjunction of continuous functors of sites with fully faithful left
adjoint, the induced adjunction on sheaves has invertible counit. On each
object of the source site, this counit is obtained by applying the sheaf to
the opposite of the original unit, hence is an isomorphism.

The coefficient category is arbitrary. No limits, additive structure,
schemes, or fields are needed.
-/


universe uC vC uD vD uA vA

open CategoryTheory

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {G : C ⥤ D} {B : D ⥤ C} [G.IsContinuous J K] [B.IsContinuous K J]
  (A : Type uA) [Category.{vA} A] (adj : G ⊣ B) [G.Full] [G.Faithful]

/-- A fully faithful left adjoint between sites yields an invertible sheaf counit. -/
lemma sheafAdjunction_counit_isIso :
    IsIso (adj.sheafPushforwardContinuous (E := A) J K).counit := by
  have : ∀ F, IsIso ((adj.sheafPushforwardContinuous (E := A) J K).counit.app F) := by
    intro F
    have : ∀ V, IsIso (((sheafToPresheaf J A).map
        ((adj.sheafPushforwardContinuous (E := A) J K).counit.app F)).app V) := by
      intro V
      change IsIso (𝟙 _ ≫ F.obj.map ((adj.unit.app V.unop).op) ≫ 𝟙 _)
      infer_instance
    have : IsIso ((sheafToPresheaf J A).map
        ((adj.sheafPushforwardContinuous (E := A) J K).counit.app F)) :=
      NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf J A)
  exact NatIso.isIso_of_isIso_app _

end EtaleCohomology.Sites

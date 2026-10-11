/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FinallySmall

/-!
# Stalks of restriction under an initial neighborhood functor

If a continuous functor is initial on the categories of pointed neighborhoods,
restriction of sheaves preserves the corresponding stalk. The opposite
neighborhood functor is final, so the result follows from the comparison of
colimits. The coefficient category only needs colimits of the size of the
points; no abelian structure or scheme hypothesis is used.
-/

noncomputable section

open CategoryTheory Limits

namespace EtaleCohomology.Sites

universe w uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [RepresentablyFlat F] [F.IsContinuous J K]
  (hF : CoverPreserving J K F) (Φ : K.Point.{w})
  [InitiallySmall.{w} (F ⋙ Φ.fiber).Elements]
  (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{w, w} A]
  [(Functor.Elements.precomp F Φ.fiber).Initial]

/-- Restriction along a continuous functor preserves the stalk when the induced
functor on pointed neighborhoods is initial. -/
def restrictionComapStalkIso :
    F.sheafPushforwardContinuous A J K ⋙ (Φ.comap F hF).sheafFiber ≅ Φ.sheafFiber := by
  let : HasColimitsOfShape (F ⋙ Φ.fiber).Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _
  exact Functor.isoWhiskerLeft
    (sheafToPresheaf K A ⋙
      (Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π Φ.fiber).op)
    (Functor.Final.colimIso (Functor.Elements.precomp F Φ.fiber).op)

end EtaleCohomology.Sites

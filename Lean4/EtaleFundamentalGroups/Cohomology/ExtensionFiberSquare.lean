/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.ExtensionFibers
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The sheaf of lifts is an actual categorical fiber

The sectionwise construction used for extension monodromy satisfies the
pullback universal property in the category of étale sheaves. This allows
exact inverse image to transport the original sheaf of lifts.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- The actual singleton sheaf, used as the source of a global section. -/
def extensionFiberTerminal (X : Scheme.{u}) : Sheaf X.smallEtaleTopology (Type u) :=
  Sheaf.terminal X.smallEtaleTopology Types.isTerminalPUnit

variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})

/-- The original global quotient section, as a morphism from the singleton sheaf. -/
def extensionFiberSection :
    extensionFiberTerminal X ⟶
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₃ :=
  ⟨t⟩

/-- Forget the condition on a section of the sheaf of lifts. -/
def extensionFiberInclusion :
    extensionFiber S t ⟶
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₂ :=
  ⟨(extensionFiberSubfunctor S t).ι⟩

/-- The existing lift sheaf is the categorical inverse image of its quotient section. -/
theorem extensionFiber_isPullback :
    IsPullback (extensionFiberInclusion S t)
      ((Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit).from
        (extensionFiber S t))
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map S.g)
      (extensionFiberSection S t) := by
  let T := Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit
  apply IsPullback.mk'
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro z
    exact z.property
  · intro B a b hab _
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k => k.hom.app U z) hab
  · intro B a b hab
    let l : B ⟶ extensionFiber S t :=
      ⟨{ app := fun U => ↾fun z =>
            ⟨a.hom.app U z, by
              have he := congrArg (fun k => k.hom.app U z) hab
              change S.g.hom.app U (a.hom.app U z) =
                t.app U (b.hom.app U z) at he
              exact he.trans (congrArg (t.app U)
                (@Subsingleton.elim PUnit inferInstance (b.hom.app U z) PUnit.unit))⟩
          , naturality := by
            intro U V k
            apply ConcreteCategory.hom_ext
            intro z
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (a.hom.naturality k) z }⟩
    refine ⟨l, ?_, T.hom_ext _ _⟩
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro z
    rfl

end EtaleFundamentalGroups.Cohomology

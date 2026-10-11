/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Action.Continuous

/-!
# Fullness of restriction for continuous actions

Restriction of continuous actions along a surjective continuous monoid
homomorphism is full.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory.ContAction

variable (V : Type u) [Category.{w} V]
variable {FV : V → V → Type w} {CV : V → Type v}
variable [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
variable [ConcreteCategory V FV] [HasForget₂ V TopCat]
variable {G H : Type*} [Monoid G] [TopologicalSpace G]
variable [Monoid H] [TopologicalSpace H]

/-- Restriction of continuous actions is faithful. -/
instance resFaithful (f : G →ₜ* H) :
    (ContAction.res V f).Faithful := by
  change (ObjectProperty.lift (Action.isContinuous V G)
    ((Action.isContinuous V H).ι ⋙ Action.res V f.toMonoidHom) _).Faithful
  let : (((Action.isContinuous V H).ι ⋙ Action.res V f.toMonoidHom)).Faithful :=
    Functor.Faithful.comp (Action.isContinuous V H).ι (Action.res V f.toMonoidHom)
  exact Functor.Faithful.of_comp_iso
    ((Action.isContinuous V G).liftCompιIso
      ((Action.isContinuous V H).ι ⋙ Action.res V f.toMonoidHom) _)

/-- Restriction of continuous actions along a surjective continuous monoid
homomorphism is full. -/
lemma full_res (f : G →ₜ* H) (hf : Function.Surjective f) :
    (ContAction.res V f).Full := by
  let : (Action.res V f.toMonoidHom).Full :=
    Action.full_res V f.toMonoidHom hf
  change (ObjectProperty.lift (Action.isContinuous V G)
    ((Action.isContinuous V H).ι ⋙ Action.res V f.toMonoidHom) _).Full
  let : (((Action.isContinuous V H).ι ⋙ Action.res V f.toMonoidHom)).Full :=
    Functor.Full.comp (Action.isContinuous V H).ι (Action.res V f.toMonoidHom)
  exact Functor.Full.of_comp_faithful_iso
    ((Action.isContinuous V G).liftCompιIso
      ((Action.isContinuous V H).ι ⋙ Action.res V f.toMonoidHom) _)

end CategoryTheory.ContAction

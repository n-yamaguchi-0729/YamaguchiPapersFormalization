/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Galois.Action

/-!
# Connected objects and transitive fiber actions

For a fiber functor on a Galois category, an object with nonempty fiber is
connected if the canonical fundamental-group action on its fiber is
pretransitive.
-/

@[expose] public section

universe u₁ u₂ w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

open Limits _root_.CategoryTheory.Functor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- An object with nonempty fiber is connected if the canonical `Aut F`-action
on its fiber is pretransitive. -/
theorem FiberFunctor.isConnected_of_isPretransitive
    (X : C) [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] :
    IsConnected X := by
  have : IsConnected ((functorToAction F).obj X) :=
    FintypeCat.Action.isConnected_of_transitive (Aut F) (F.obj X)
  refine ⟨(not_initial_iff_fiber_nonempty F X).mpr inferInstance, ?_⟩
  intro Y i _ hY
  have hY_nonempty : Nonempty (F.obj Y) :=
    (not_initial_iff_fiber_nonempty F Y).mp hY
  have hY_action_not_initial :
      IsInitial ((functorToAction F).obj Y) → False :=
    (not_initial_iff_fiber_nonempty
      (Action.forget FintypeCat (Aut F))
      ((functorToAction F).obj Y)).mpr hY_nonempty
  have : Mono ((functorToAction F).map i) :=
    map_mono (functorToAction F) i
  have : IsIso ((functorToAction F).map i) :=
    IsConnected.noTrivialComponent
      ((functorToAction F).obj Y)
      ((functorToAction F).map i)
      hY_action_not_initial
  exact isIso_of_reflects_iso i (functorToAction F)

end CategoryTheory.PreGaloisCategory

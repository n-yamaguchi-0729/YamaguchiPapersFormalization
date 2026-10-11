/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Action.Continuous

/-!
# The identity forgetful functor on `TopCat`

`HasForget₂` deliberately has no general self-instance.  The continuous-action
API nevertheless needs the canonical identity forgetful functor when its
ambient concrete category is `TopCat` itself.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe u v

/-- The canonical identity forgetful functor from `TopCat` to itself. -/
instance topCatHasForget₂Self : HasForget₂ TopCat.{u} TopCat.{u} where
  forget₂ := 𝟭 TopCat.{u}

namespace DiscreteContAction

-- `DiscreteContAction` is a non-reducible full subcategory in mathlib.  Make
-- its canonical concrete and forgetful instances available for `TopCat`
-- without relying on consumers unfolding that definition during search.
instance topCatConcrete {G : Type v} [Monoid G] [TopologicalSpace G] :
    ConcreteCategory (DiscreteContAction TopCat.{u} G)
      (fun S T => Action.HomSubtype TopCat.{u} G S.obj.obj T.obj.obj) := by
  exact ObjectProperty.FullSubcategory.concreteCategory
    (ContAction.IsDiscrete (V := TopCat.{u}) (G := G))

instance topCatHasForget₂ {G : Type v} [Monoid G] [TopologicalSpace G] :
    HasForget₂ (DiscreteContAction TopCat.{u} G) TopCat.{u} := by
  exact HasForget₂.trans
    (ObjectProperty.FullSubcategory (ContAction.IsDiscrete (V := TopCat.{u}) (G := G)))
    (ContAction TopCat.{u} G) TopCat.{u}

/-- The carrier of a discrete continuous `TopCat`-action has the original
multiplicative action. -/
instance carrierMulAction {G : Type v} [Monoid G] [TopologicalSpace G]
    (S : DiscreteContAction TopCat.{u} G) :
    MulAction G
      ((forget₂ (DiscreteContAction TopCat.{u} G) TopCat.{u}).obj S) := by
  change MulAction G ((forget₂ (Action TopCat.{u} G) TopCat.{u}).obj S.obj.obj)
  infer_instance

end DiscreteContAction

end CategoryTheory

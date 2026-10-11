/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Nyll.EtaleFundamentalGroups.ContinuousActions.FiniteLimitsAndColimits

/-!
# Exactness of fiber functors

Fiber functors from Galois categories preserve finite colimits.  This follows
from the equivalence with finite continuous actions and exactness of the
underlying-set functor on those actions.
-/

@[expose] public section

universe u₁ u₂ w

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory.FiberFunctor

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- A fiber functor from a Galois category preserves finite colimits. -/
noncomputable instance preservesFiniteColimits :
    PreservesFiniteColimits F := by
  let E := functorToContAction F
  let U := forget₂ (ContAction FintypeCat.{w} (Aut F)) FintypeCat
  have : PreservesFiniteColimits (E ⋙ U) := by
    apply comp_preservesFiniteColimits
  let e : E ⋙ U ≅ F :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  exact preservesFiniteColimits_of_natIso e

end CategoryTheory.PreGaloisCategory.FiberFunctor

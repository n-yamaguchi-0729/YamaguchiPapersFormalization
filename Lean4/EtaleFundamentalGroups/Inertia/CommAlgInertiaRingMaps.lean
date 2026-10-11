/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Ring maps underlying intrinsic inertia

Extracts the coefficient ring map of an intrinsic inertia element and proves that this ring map
determines the element.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- An intrinsic inertia element's literal coefficient ring map. -/
def commAlgIdealInertiaRingHom
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B)
    (σ : commAlgIdealInertiaGroup A B Q) : B →+* B :=
  σ.val.toRingHom

/-- The literal coefficient map determines the intrinsic inertia element. -/
theorem commAlgIdealInertiaRingHom_injective
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B) :
    Function.Injective (commAlgIdealInertiaRingHom A B Q) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro b
  exact congrArg (fun f : B →+* B => f.toFun b) h

end EtaleFundamentalGroups.Inertia

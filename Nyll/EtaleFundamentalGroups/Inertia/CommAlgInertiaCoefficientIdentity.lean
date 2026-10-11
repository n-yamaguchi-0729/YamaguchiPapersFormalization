/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.SchemeTheory.Normalization.NativeAutomorphismRingMaps
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Detecting intrinsic inertia identity on coefficients

The native inertia subgroup retains its underlying coefficient automorphism.
Consequently its identity is detected by the literal coefficient ring map.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- An intrinsic inertia element is the identity exactly when its actual
coefficient ring map is the identity. -/
theorem commAlgIdealInertia_eq_one_iff_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier)
    (τ : (commAlgIdealInertiaGroup A B Q).carrier) :
    τ = 1 ↔ commAlgAutomorphismRingHom A B τ.val = RingHom.id B.carrier := by
  constructor
  · intro hτ
    rw [hτ]
    rfl
  · intro hτ
    apply Subtype.ext
    apply AlgEquiv.ext
    intro b
    exact RingHom.congr_fun hτ b

end EtaleFundamentalGroups.Inertia

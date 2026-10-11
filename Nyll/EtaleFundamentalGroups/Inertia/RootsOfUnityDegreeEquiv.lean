/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Transport of root groups along equality of their degrees

The transport keeps the actual unit. Its scalar computation, inverse, and
homomorphism structure are built together, before any field tower appears.
-/

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Equality of degrees identifies their root groups without changing units. -/
def rootsOfUnityDegreeEquiv (R : Type u) [CommMonoid R]
    {m n : ℕ} (h : m = n) : rootsOfUnity m R ≃* rootsOfUnity n R where
  toFun ζ := ⟨ζ.val, h ▸ ζ.property⟩
  invFun ζ := ⟨ζ.val, h.symm ▸ ζ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Degree transport preserves the underlying unit literally. -/
theorem rootsOfUnityDegreeEquiv_val (R : Type u) [CommMonoid R]
    {m n : ℕ} (h : m = n) (ζ : rootsOfUnity m R) :
    ((rootsOfUnityDegreeEquiv R h).toFun ζ).val = ζ.val := rfl

end EtaleFundamentalGroups.Inertia

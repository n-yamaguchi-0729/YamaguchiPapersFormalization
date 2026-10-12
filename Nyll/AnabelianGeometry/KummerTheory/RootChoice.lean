/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.RootCocycle

/-!
# Independence of radical cocycles from the choice of root

Over a base containing the relevant roots of unity, replacing a radical by
another root of the same power equation leaves its Galois cocycle unchanged.
-/

namespace AnabelianGeometry.KummerTheory

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- Roots of the same power equation have identical radical cocycles when
all roots of unity of that order lie in the base field. -/
theorem rootRatio_eq_of_pow_eq {r s : L} (hr : r ≠ 0) (hs : s ≠ 0)
    {n : ℕ} (hpow : s ^ n = r ^ n)
    (hroots : ∀ ξ : L, ξ ^ n = 1 → ∃ b : K, algebraMap K L b = ξ)
    (σ : L ≃ₐ[K] L) : rootRatio r σ = rootRatio s σ := by
  have hsr : (s / r) ^ n = 1 := by
    rw [div_pow, hpow, div_self (pow_ne_zero n hr)]
  obtain ⟨b, hb⟩ := hroots (s / r) hsr
  have hfixed : σ (s / r) = s / r := by rw [← hb, σ.commutes]
  rw [map_div₀] at hfixed
  have hσr : σ r ≠ 0 := (map_ne_zero σ).mpr hr
  apply (div_eq_div_iff hr hs).mpr
  calc
    σ r * s = s * σ r := mul_comm _ _
    _ = σ s * r := ((div_eq_div_iff hσr hr).mp hfixed).symm

/-- Taking a power of the radical takes the same power of its cocycle. -/
theorem rootRatio_pow (r : L) (σ : L ≃ₐ[K] L) (m : ℕ) :
    rootRatio (r ^ m) σ = rootRatio r σ ^ m := by
  change σ (r ^ m) / r ^ m = (σ r / r) ^ m
  rw [map_pow, div_pow]

end AnabelianGeometry.KummerTheory

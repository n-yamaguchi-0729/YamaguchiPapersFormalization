/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.CyclotomicPowerDescent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Data.Int.GCD

/-!
# Exact power descent under coprimality

Norms descend powers across extensions of coprime degree. A central
cyclotomic automorphism gives a second exact descent criterion when its
displacement is coprime to the exponent.
-/

namespace AnabelianGeometry.KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A power relation over a finite extension of degree coprime to its
exponent already has a witness over the original field. -/
theorem exists_pow_eq_of_coprime_finrank [FiniteDimensional K L]
    (n : ℕ) (a : K) (r : L) (hr : r ^ n = algebraMap K L a)
    (hcop : (Module.finrank K L).Coprime n) :
    ∃ c : K, c ^ n = a := by
  apply (pow_mem_range_pow_of_coprime hcop a).mp
  refine ⟨Algebra.norm K r, ?_⟩
  change (Algebra.norm K r) ^ n = a ^ Module.finrank K L
  rw [← map_pow, hr, Algebra.norm_algebraMap]

/-- A cyclotomic displacement prime to the exponent removes the entire
power-class kernel, without a residual roots-of-unity factor. -/
theorem exists_pow_eq_of_coprime_central_cyclotomic [IsGalois K L]
    {r : L} (hr : r ≠ 0) {n m : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ : L ≃ₐ[K] L)
    (hcentral : ∀ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (hσ : ∀ ξ : L, ξ ^ n = 1 → σ ξ = ξ ^ (m + 1))
    (hcop : m.Coprime n) :
    ∃ c : K, c ^ n = a := by
  apply (pow_mem_range_pow_of_coprime hcop a).mp
  exact exists_power_eq_of_central_cyclotomic hr ha σ hcentral hσ

end AnabelianGeometry.KummerTheory

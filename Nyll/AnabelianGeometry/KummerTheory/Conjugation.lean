/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.RootCocycle
import Mathlib.Tactic.Ring

/-!
# Cyclotomic conjugation of radical automorphisms

Conjugation transports a radical ratio by the action on roots of unity.
Only the automorphism being conjugated is required to fix those roots;
the conjugating automorphism may act nontrivially on them. This is the
finite-level Kummer calculation behind the cyclotomic action on inertia.
-/

namespace AnabelianGeometry.KummerTheory

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- Conjugation of an automorphism fixing the relevant roots of unity acts
on its radical ratio by the conjugating automorphism's cyclotomic action. -/
theorem rootRatio_conjugate {r : L} (hr : r ≠ 0) {n : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ τ : L ≃ₐ[K] L)
    (hτ : ∀ ξ : L, ξ ^ n = 1 → τ ξ = ξ) :
    rootRatio r (σ * τ * σ⁻¹) = σ (rootRatio r τ) := by
  rw [rootRatio_mul hr (σ * τ) σ⁻¹, rootRatio_mul hr σ τ]
  change σ (τ (rootRatio r σ⁻¹)) * (σ (rootRatio r τ) * rootRatio r σ) =
    σ (rootRatio r τ)
  rw [hτ _ (rootRatio_pow_eq_one hr ha σ⁻¹)]
  calc
    σ (rootRatio r σ⁻¹) * (σ (rootRatio r τ) * rootRatio r σ) =
        σ (rootRatio r τ) * (σ (rootRatio r σ⁻¹) * rootRatio r σ) := by ring
    _ = σ (rootRatio r τ) := by
      rw [← rootRatio_mul hr, mul_inv_cancel]
      change σ (rootRatio r τ) * (r / r) = σ (rootRatio r τ)
      rw [div_self hr, mul_one]

/-- If the action on the relevant roots of unity is given by an exponent,
conjugation raises the radical ratio to that same exponent. -/
theorem rootRatio_conjugate_eq_pow {r : L} (hr : r ≠ 0) {n m : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ τ : L ≃ₐ[K] L)
    (hτ : ∀ ξ : L, ξ ^ n = 1 → τ ξ = ξ)
    (hσ : ∀ ξ : L, ξ ^ n = 1 → σ ξ = ξ ^ m) :
    rootRatio r (σ * τ * σ⁻¹) = rootRatio r τ ^ m := by
  rw [rootRatio_conjugate hr ha σ τ hτ]
  exact hσ _ (rootRatio_pow_eq_one hr ha τ)

/-- On an automorphism fixing roots of unity, powers of the automorphism
correspond to powers of its radical ratio. -/
theorem rootRatio_aut_pow {r : L} (hr : r ≠ 0) {n : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (τ : L ≃ₐ[K] L)
    (hτ : ∀ ξ : L, ξ ^ n = 1 → τ ξ = ξ) (m : ℕ) :
    rootRatio r (τ ^ m) = rootRatio r τ ^ m := by
  induction m with
  | zero =>
    simp only [pow_zero]
    change r / r = 1
    exact div_self hr
  | succ m hm =>
    rw [pow_succ', rootRatio_mul hr,
      hτ _ (rootRatio_pow_eq_one hr ha (τ ^ m)), hm, pow_succ]

end AnabelianGeometry.KummerTheory

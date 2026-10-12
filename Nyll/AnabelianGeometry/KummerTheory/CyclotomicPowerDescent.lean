/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.RootCocycle
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Tactic.Ring

/-!
# Descent of powers from a cyclotomic action

A central Galois automorphism acting on n-th roots of unity by the
(m + 1)-st power forces an n-th radical from the base to descend after
raising its power class to m. The proof is the explicit radical-cocycle
calculation and the Galois fixed-field theorem. It does not assume a
uniform bound on m or a number-field cyclotomic image theorem.
-/

open scoped IsMulCommutative

namespace AnabelianGeometry.KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A central automorphism with specified cyclotomic action controls the
Galois change of its own radical ratio. -/
theorem rootRatio_central_cyclotomic
    {r : L} (hr : r ≠ 0) {n m : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ τ : L ≃ₐ[K] L)
    (hcomm : σ * τ = τ * σ)
    (hσ : ∀ ξ : L, ξ ^ n = 1 → σ ξ = ξ ^ (m + 1)) :
    τ (rootRatio r σ) = rootRatio r τ ^ m * rootRatio r σ := by
  apply mul_right_cancel₀ (rootRatio_ne_zero hr τ)
  calc
    τ (rootRatio r σ) * rootRatio r τ = rootRatio r (τ * σ) :=
      (rootRatio_mul hr τ σ).symm
    _ = rootRatio r (σ * τ) := congrArg (rootRatio r) hcomm.symm
    _ = σ (rootRatio r τ) * rootRatio r σ := rootRatio_mul hr σ τ
    _ = (rootRatio r τ ^ m * rootRatio r σ) * rootRatio r τ := by
      rw [hσ _ (rootRatio_pow_eq_one hr ha τ), pow_succ]
      ring

/-- An explicit root-of-unity correction makes a power of the radical
fixed by every Galois automorphism. -/
theorem radical_power_div_ratio_fixed
    {r : L} (hr : r ≠ 0) {n m : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ : L ≃ₐ[K] L)
    (hcentral : ∀ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (hσ : ∀ ξ : L, ξ ^ n = 1 → σ ξ = ξ ^ (m + 1))
    (τ : L ≃ₐ[K] L) :
    τ (r ^ m / rootRatio r σ) = r ^ m / rootRatio r σ := by
  have ht : τ r = rootRatio r τ * r := (div_mul_cancel₀ (τ r) hr).symm
  rw [map_div₀, map_pow, rootRatio_central_cyclotomic hr ha σ τ (hcentral τ) hσ,
    ht, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero m (rootRatio_ne_zero hr τ))

/-- The cyclotomic displacement m annihilates the kernel of the n-th power
class map for radicals contained in this Galois extension. -/
theorem exists_power_eq_of_central_cyclotomic [IsGalois K L]
    {r : L} (hr : r ≠ 0) {n m : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ : L ≃ₐ[K] L)
    (hcentral : ∀ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (hσ : ∀ ξ : L, ξ ^ n = 1 → σ ξ = ξ ^ (m + 1)) :
    ∃ c : K, c ^ n = a ^ m := by
  obtain ⟨c, hc⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := K) (K := L) (r ^ m / rootRatio r σ)).mpr
        (radical_power_div_ratio_fixed hr ha σ hcentral hσ)
  refine ⟨c, (algebraMap K L).injective ?_⟩
  rw [map_pow, hc, div_pow, ← pow_mul, Nat.mul_comm m n, pow_mul,
    ha, rootRatio_pow_eq_one hr ha σ, div_one, map_pow]

/-- In an abelian Galois extension, the same calculation gives an actual
unit of the original field witnessing the annihilated power class. -/
theorem exists_unit_power_eq_of_abelian_cyclotomic [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (n : ℕ+) (m : ℕ) (a : Kˣ) (r : L) (hr : r ≠ 0)
    (ha : r ^ (n : ℕ) = algebraMap K L (a : K)) (σ : L ≃ₐ[K] L)
    (hσ : ∀ ξ : L, ξ ^ (n : ℕ) = 1 → σ ξ = ξ ^ (m + 1)) :
    ∃ c : Kˣ, c ^ (n : ℕ) = a ^ m := by
  obtain ⟨c, hc⟩ := exists_power_eq_of_central_cyclotomic hr ha σ
    (fun τ => mul_comm σ τ) hσ
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.ne_zero] at hc
    exact (pow_ne_zero m a.ne_zero) hc.symm
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  exact hc

end AnabelianGeometry.KummerTheory

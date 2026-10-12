/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Galois cocycles of radicals

The quotient of a conjugate radical by the original radical satisfies the
crossed-homomorphism law. Its values are roots of unity when the radical has
a power in the base field. When those roots of unity are in the base, the
crossed law becomes an ordinary multiplicative character law.
-/

namespace AnabelianGeometry.KummerTheory

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The multiplicative change in a radical under a base-field automorphism. -/
def rootRatio (r : L) (σ : L ≃ₐ[K] L) : L := σ r / r

/-- The ratio of a conjugate of a nonzero radical is nonzero. -/
theorem rootRatio_ne_zero {r : L} (hr : r ≠ 0) (σ : L ≃ₐ[K] L) :
    rootRatio r σ ≠ 0 :=
  div_ne_zero ((map_ne_zero σ).mpr hr) hr

/-- A radical ratio detects precisely whether the radical is fixed. -/
theorem rootRatio_eq_one_iff {r : L} (hr : r ≠ 0) (σ : L ≃ₐ[K] L) :
    rootRatio r σ = 1 ↔ σ r = r := by
  exact div_eq_one_iff_eq hr

/-- If the `n`-th power is in the base field, each radical ratio is an
`n`-th root of unity. -/
theorem rootRatio_pow_eq_one {r : L} (hr : r ≠ 0) {n : ℕ} {a : K}
    (ha : r ^ n = algebraMap K L a) (σ : L ≃ₐ[K] L) :
    rootRatio r σ ^ n = 1 := by
  have hnz : algebraMap K L a ≠ 0 := ha ▸ pow_ne_zero n hr
  rw [rootRatio, div_pow, ← map_pow, ha, σ.commutes, div_self hnz]

/-- The crossed-homomorphism law, without assuming roots of unity are fixed. -/
theorem rootRatio_mul {r : L} (hr : r ≠ 0) (σ τ : L ≃ₐ[K] L) :
    rootRatio r (σ * τ) = σ (rootRatio r τ) * rootRatio r σ := by
  change σ (τ r) / r = σ (τ r / r) * (σ r / r)
  rw [map_div₀]
  have hs : σ r ≠ 0 := (map_ne_zero σ).mpr hr
  field_simp [hr, hs]

/-- Base-field roots of unity turn the radical cocycle into a character. -/
theorem rootRatio_mul_of_roots_in_base {r : L} (hr : r ≠ 0)
    {n : ℕ} {a : K} (ha : r ^ n = algebraMap K L a)
    (hroots : ∀ ξ : L, ξ ^ n = 1 → ∃ b : K, algebraMap K L b = ξ)
    (σ τ : L ≃ₐ[K] L) :
    rootRatio r (σ * τ) = rootRatio r σ * rootRatio r τ := by
  obtain ⟨b, hb⟩ := hroots (rootRatio r τ) (rootRatio_pow_eq_one hr ha τ)
  rw [rootRatio_mul hr, ← hb, σ.commutes, mul_comm]

/-- The radical ratio is trivial exactly on the subgroup fixing the generated
intermediate field pointwise. No finite-degree or irreducibility hypothesis
is needed for this kernel description. -/
theorem mem_fixingSubgroup_adjoin_iff_rootRatio_eq_one
    {r : L} (hr : r ≠ 0) (σ : L ≃ₐ[K] L) :
    σ ∈ (IntermediateField.adjoin K ({r} : Set L)).fixingSubgroup ↔
      rootRatio r σ = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff, rootRatio_eq_one_iff hr]
  constructor
  · intro h
    exact h r (IntermediateField.subset_adjoin K _ (Set.mem_singleton r))
  · intro h x hx
    induction hx using IntermediateField.adjoin_induction K with
    | mem x hx =>
      have hx' : x = r := Set.mem_singleton_iff.mp hx
      subst x
      exact h
    | algebraMap x => exact σ.commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]

end AnabelianGeometry.KummerTheory

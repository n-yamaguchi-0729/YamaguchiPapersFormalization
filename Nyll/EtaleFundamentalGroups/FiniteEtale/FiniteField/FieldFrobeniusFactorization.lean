/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Field Frobenius Factorization

A single Frobenius power sends every element of a finite purely inseparable
extension into the original field.
-/

noncomputable section
open scoped BigOperators
universe u
namespace EtaleFundamentalGroups

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable [IsPurelyInseparable k L] [FiniteDimensional k L]
variable (p : ℕ) [ExpChar k p] [ExpChar L p]

/-- A single Frobenius power sends every element of a finite purely inseparable
extension into the original field. -/
theorem exists_uniform_purelyInseparable_exponent :
    ∃ n : ℕ, ∀ x : L, x ^ p ^ n ∈ (algebraMap k L).range := by
  classical
  let b := Module.finBasis k L
  choose e he using fun i : Fin (Module.finrank k L) ↦
    IsPurelyInseparable.pow_mem k p (b i)
  let n := Finset.univ.sup e
  have hb (i : Fin (Module.finrank k L)) : (b i) ^ p ^ n ∈ (algebraMap k L).range := by
    have hi : e i ≤ n := Finset.le_sup (Finset.mem_univ i)
    have h := (algebraMap k L).range.pow_mem (he i) (p ^ (n - e i))
    rw [← pow_mul, ← pow_add, Nat.add_sub_of_le hi] at h
    exact h
  refine ⟨n, fun x ↦ ?_⟩
  rw [← b.sum_repr x, sum_pow_char_pow]
  apply (algebraMap k L).range.sum_mem
  intro i _
  rw [Algebra.smul_def, mul_pow, ← map_pow]
  exact (algebraMap k L).range.mul_mem ⟨_, rfl⟩ (hb i)

/-- The Frobenius power factors in both directions through the original field. -/
theorem exists_purelyInseparable_frobenius_factorization :
    ∃ (n : ℕ) (σ : L →+* k),
      (algebraMap k L).comp σ = iterateFrobenius L p n ∧
        σ.comp (algebraMap k L) = iterateFrobenius k p n := by
  classical
  obtain ⟨n, hn⟩ := exists_uniform_purelyInseparable_exponent k L p
  choose s hs using hn
  let σ : L →+* k :=
    { toFun := s
      map_one' := (algebraMap k L).injective (by rw [hs, one_pow, map_one])
      map_mul' := fun x y ↦ (algebraMap k L).injective (by rw [hs, map_mul, hs, hs, mul_pow])
      map_zero' := (algebraMap k L).injective (by
        rw [hs, zero_pow (expChar_pow_pos k p n).ne', map_zero])
      map_add' := fun x y ↦ (algebraMap k L).injective (by
        rw [hs, map_add, hs, hs, add_pow_expChar_pow]) }
  refine ⟨n, σ, RingHom.ext hs, RingHom.ext fun x ↦ ?_⟩
  apply (algebraMap k L).injective
  change algebraMap k L (s (algebraMap k L x)) = algebraMap k L (x ^ p ^ n)
  rw [hs, map_pow]

end EtaleFundamentalGroups

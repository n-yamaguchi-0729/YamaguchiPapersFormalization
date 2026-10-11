/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
# Module finrank add alternating Sum finrank eq of finite complex
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.HomologicalAlgebra.Proofs.EulerCharacteristicFinrank

universe u

namespace FinrankComplexW4

theorem telescope (n : ℕ) (κ r d h : ℕ → ℤ) (h0 : ℤ)
    (hd : ∀ i, d i = κ i + r i) (hh : ∀ i, h i = κ (i + 1) - r i) (hh0 : h0 = κ 0)
    (hrn : r n = 0) :
    h0 + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * h i =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * d i := by
  rw [Finset.sum_range_succ']
  have key : ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ (i + 1) * r (i + 1) + (-1 : ℤ) ^ (i + 1) * r i) =
      (-1) ^ n * r n - (-1) ^ 0 * r 0 := by
    rw [← Finset.sum_range_sub (fun i => (-1 : ℤ) ^ i * r i) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e1 : ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * h i =
      ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ (i + 1) * κ (i + 1) - (-1 : ℤ) ^ (i + 1) * r i) :=
    Finset.sum_congr rfl fun i _ => by rw [hh]; ring
  have e2 : ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * d (i + 1) =
      ∑ i ∈ Finset.range n, ((-1 : ℤ) ^ (i + 1) * κ (i + 1) + (-1 : ℤ) ^ (i + 1) * r (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [hd]; ring
  rw [e1, e2, Finset.sum_sub_distrib, Finset.sum_add_distrib, hh0, hd 0]
  rw [Finset.sum_add_distrib, hrn] at key
  linear_combination (-1 : ℤ) * key

end FinrankComplexW4

open FinrankComplexW4 in
theorem _root_.Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex
    (k : Type u) [Field k]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module k (K i)] [∀ i, Module.Finite k (K i)]
    (δ : ∀ i, K i →ₗ[k] K (i + 1)) (hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (K i))
    (H0 : Type u) [AddCommGroup H0] [Module k H0] (e₀ : H0 ≃ₗ[k] LinearMap.ker (δ 0))
    (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module k (H i)]
    (π : ∀ i, LinearMap.ker (δ (i + 1)) →ₗ[k] H i) (hπ : ∀ i, Function.Surjective (π i))
    (hπker : ∀ i, LinearMap.ker (π i) =
      (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) :
    (Module.finrank k H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank k (H i)
      : ℤ) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank k (K i) : ℤ) := by
  have hle : ∀ i, LinearMap.range (δ i) ≤ LinearMap.ker (δ (i + 1)) := by
    intro i x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker]
    have h := congrArg (fun f => f y) (hδδ i)
    simpa using h
  have hd : ∀ i, (Module.finrank k (K i) : ℤ) =
      (Module.finrank k (LinearMap.ker (δ i)) : ℤ) + (Module.finrank k (LinearMap.range (δ i)) :
        ℤ) := by
    intro i
    have h := LinearMap.finrank_range_add_finrank_ker (δ i)
    omega
  have hh : ∀ i, (Module.finrank k (H i) : ℤ) =
      (Module.finrank k (LinearMap.ker (δ (i + 1))) : ℤ) - (Module.finrank k (LinearMap.range (δ
        i)) : ℤ) := by
    intro i
    have h1 := LinearMap.finrank_range_add_finrank_ker (π i)
    rw [LinearMap.range_eq_top.mpr (hπ i), finrank_top, hπker i,
      (Submodule.comapSubtypeEquivOfLe (hle i)).finrank_eq] at h1
    omega
  have hh0 : (Module.finrank k H0 : ℤ) = (Module.finrank k (LinearMap.ker (δ 0)) : ℤ) := by
    rw [e₀.finrank_eq]
  have hrn : (Module.finrank k (LinearMap.range (δ n)) : ℤ) = 0 := by
    have := hbdd (n + 1) (Nat.lt_succ_self n)
    have hδn : δ n = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    rw [hδn, LinearMap.range_zero, finrank_bot]
    rfl
  exact telescope n (fun i => (Module.finrank k (LinearMap.ker (δ i)) : ℤ))
    (fun i => (Module.finrank k (LinearMap.range (δ i)) : ℤ))
    (fun i => (Module.finrank k (K i) : ℤ)) (fun i => (Module.finrank k (H i) : ℤ))
    (Module.finrank k H0 : ℤ) hd hh hh0 hrn
end AlgebraicCurves.Foundations.HomologicalAlgebra.Proofs.EulerCharacteristicFinrank
end ProofImplementation

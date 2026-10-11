/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Divisor exists pullback Along single one eq sum
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_exists_pullbackAlong_single_one_eq_sum

namespace PullbackEnum

theorem exists_fin_sum_eq_sum_nsmul {α M : Type*} [AddCommMonoid M] (s : Finset α)
    (e : α → ℕ) (f : α → M) :
    ∀ n : ℕ, ∑ a ∈ s, e a = n →
      ∃ W : Fin n → α, (∀ i, W i ∈ s) ∧ ∑ i, f (W i) = ∑ a ∈ s, e a • f a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n hn
    rw [Finset.sum_empty] at hn
    subst hn
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩
  | insert a s ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨W, hW, hsum⟩ := ih _ rfl
    subst hn
    refine ⟨Fin.append (fun _ : Fin (e a) => a) W, fun i => ?_, ?_⟩
    · induction i using Fin.addCases with
      | left k =>
        rw [Fin.append_left]
        exact Finset.mem_insert_self a s
      | right k =>
        rw [Fin.append_right]
        exact Finset.mem_insert_of_mem (hW k)
    · rw [Finset.sum_insert ha, ← hsum, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin]

end PullbackEnum

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.exists_pullbackAlong_single_one_eq_sum
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : AlgebraicCurve.FundamentalIdentityAlong K
      φ hφ)
    (P : AlgebraicCurve.Place K F) (hdegP : P.deg = 1)
    (hdeg1 : ∀ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = P → w.deg = 1)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n) :
    ∃ W : Fin n → AlgebraicCurve.Place K F',
      AlgebraicCurve.Divisor.pullbackAlong φ hφ (Finsupp.single P 1) = ∑ i, Finsupp.single (W i) 1 ∧
        ∀ i, (W i).restrictAlong φ hφ = P := by
  classical
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : FundamentalIdentity K F F' := hFI
  have hcount : ∑ w ∈ Place.fiberAlong φ hφ P, w.ramificationIndexAlong φ = n := by
    have h := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') P
    rw [hdegP, Nat.cast_one, mul_one] at h
    have h' : ∑ w ∈ P.fiber F', (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
      rw [← h]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hdeg1 w (Place.mem_fiber.1 hw), Nat.cast_one, mul_one]
    have h'' : ((∑ w ∈ Place.fiberAlong φ hφ P, w.ramificationIndexAlong φ : ℕ) : ℤ) = (n : ℤ) := by
      rw [← hn]
      push_cast
      exact h'
    exact_mod_cast h''
  obtain ⟨W, hWmem, hWsum⟩ := PullbackEnum.exists_fin_sum_eq_sum_nsmul (Place.fiberAlong φ hφ P)
    (fun w => w.ramificationIndexAlong φ) (fun w => (Finsupp.single w (1 : ℤ) : Divisor K F')) n
      hcount
  refine ⟨W, ?_, fun i => Place.mem_fiberAlong.1 (hWmem i)⟩
  rw [Divisor.pullbackAlong_single, hWsum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [one_mul, Finsupp.smul_single, nsmul_eq_mul, mul_one]
end AlgebraicCurves.Divisors.Proofs.Divisor_exists_pullbackAlong_single_one_eq_sum
end ProofImplementation

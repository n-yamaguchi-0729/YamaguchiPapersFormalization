/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
A torsion divisor class yields a rational function with the prescribed multiple of its divisor.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.exists_ord_eq_mul_of_nsmul_mk_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : ↥(Divisor.degZero (K := K) (F := F))) (n : ℕ) (h : n • Pic0.mk D = 0) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by
  have hmk : ∀ m : ℕ, Pic0.mk (m • D) = m • Pic0.mk D := by
    intro m
    induction m with
    | zero => simp only [zero_nsmul, Pic0.mk_zero]
    | succ m ih => rw [succ_nsmul, Pic0.mk_add, ih, succ_nsmul]
  have h1 : Pic0.mk (n • D) = 0 := by rw [hmk, h]
  have h2 : (n • D : ↥(Divisor.degZero (K := K) (F := F))) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨f, hf, hfD⟩ := (Divisor.mem_principal.mp h2)
  refine ⟨f, hf, fun v => ?_⟩
  rw [← hfD v, AddSubgroupClass.coe_nsmul, Finsupp.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]
end JacobianVarieties.Pic0.Proofs.Pic0_exists_ord_eq_mul_of_nsmul_mk_eq_zero
end ProofImplementation

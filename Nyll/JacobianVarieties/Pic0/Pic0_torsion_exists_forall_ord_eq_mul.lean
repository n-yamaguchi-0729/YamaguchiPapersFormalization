/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Principal multiples of torsion divisor classes
-/


section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_torsion_exists_forall_ord_eq_mul


noncomputable section

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F))
    (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx : (n : ℤ) • (x : Pic0 K F) = 0 := Pic0.mem_torsion.mp x.2
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      change QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx]
  have h3 : ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h3
  have h4 : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F)) := Divisor.mem_principal.mp h3
  obtain ⟨f, hf0, hford⟩ := h4
  refine ⟨f, hf0, fun v => ?_⟩
  have := hford v
  rw [Finsupp.smul_apply, smul_eq_mul] at this
  exact this.symm

end
end JacobianVarieties.Pic0.Proofs.Pic0_torsion_exists_forall_ord_eq_mul
end ProofImplementation

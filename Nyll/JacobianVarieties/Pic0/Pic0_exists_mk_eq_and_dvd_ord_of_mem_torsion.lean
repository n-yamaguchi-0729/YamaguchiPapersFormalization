/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
Torsion divisor classes admit rational functions with orders divisible by the torsion exponent.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion

open AlgebraicCurve

private theorem exists_ord_eq_mul_of_mk_mem_torsion
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) {D : Divisor.degZero (K := K) (F := F)}
    (hD : Pic0.mk D = x) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx' : (n : ℤ) • x = 0 := Pic0.mem_torsion.mp hx
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      change QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx']
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
private theorem exists_mk_eq_and_ord_eq_mul_of_mem_torsion
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  obtain ⟨D, hD⟩ := Pic0.mk_surjective x
  obtain ⟨f, hf0, hf⟩ := exists_ord_eq_mul_of_mk_mem_torsion hx hD
  exact ⟨D, f, hD, hf0, hf⟩
theorem _root_.AlgebraicCurve.Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, (n : ℤ) ∣ v.ord f) ∧
        ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  obtain ⟨D, f, hD, hf0, hf⟩ := exists_mk_eq_and_ord_eq_mul_of_mem_torsion hx
  exact ⟨D, f, hD, hf0, fun v => ⟨(D : Divisor K F) v, hf v⟩, hf⟩

end JacobianVarieties.Pic0.Proofs.Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
end ProofImplementation

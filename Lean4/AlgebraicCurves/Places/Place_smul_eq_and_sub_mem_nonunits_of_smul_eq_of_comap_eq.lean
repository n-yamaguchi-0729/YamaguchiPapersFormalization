/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup

/-!
# Place smul eq and sub mem nonunits of smul eq of comap eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq

open AlgebraicCurve
open scoped Pointwise

theorem _root_.AlgebraicCurve.Place.smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F']
    (σ : F ≃ₐ[κ] F) (σ' : F' ≃ₐ[κ'] F')
    (hσ : ∀ f : F, σ' (algebraMap F F' f) = algebraMap F F' (σ f))
    (P : Place κ F) (P' : Place κ' F')
    (hP' : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hrat : ∀ x : F', x ∈ P'.toValuationSubring →
      ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits)
    (hfix : σ' • P' = P') :
    σ • P = P ∧ ∀ e : F, e ∈ P.toValuationSubring → σ e - e ∈ P.toValuationSubring.nonunits := by
  have hσ_inv : ∀ f : F, σ'.symm (algebraMap F F' f) = algebraMap F F' (σ.symm f) := by
    intro f
    apply σ'.injective
    rw [AlgEquiv.apply_symm_apply, hσ, AlgEquiv.apply_symm_apply]
  have mem_iff : ∀ f : F, f ∈ P.toValuationSubring ↔ algebraMap F F' f ∈ P'.toValuationSubring := by
    intro f; rw [← hP']; rfl
  have stab : ∀ y : F', y ∈ P'.toValuationSubring ↔ σ'.symm y ∈ P'.toValuationSubring := by
    intro y
    have h := congrArg AlgebraicCurve.Place.toValuationSubring hfix
    rw [AlgebraicCurve.Place.smul_toValuationSubring] at h
    conv_lhs => rw [← h]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.aut_inv]
  refine ⟨?_, ?_⟩
  · ext f
    rw [AlgebraicCurve.Place.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.aut_inv, mem_iff, mem_iff, ← hσ_inv]
    exact (stab _).symm
  · intro e he
    have hx : algebraMap F F' e ∈ P'.toValuationSubring := (mem_iff e).mp he
    obtain ⟨c, hc⟩ := hrat _ hx
    have nstab : ∀ y : F', y ∈ P'.toValuationSubring.nonunits → σ' y ∈
      P'.toValuationSubring.nonunits := by
      intro y hy
      rw [ValuationSubring.mem_nonunits_iff_or] at hy ⊢
      rcases hy with rfl | hy
      · exact Or.inl (map_zero _)
      · right
        rw [← map_inv₀]
        intro h
        exact hy (by simpa using (stab _).mp h)
    have key : σ' (algebraMap F F' e) - algebraMap F F' e ∈ P'.toValuationSubring.nonunits := by
      have hrw : σ' (algebraMap F F' e) - algebraMap F F' e =
          σ' (algebraMap F F' e - algebraMap κ' F' c) - (algebraMap F F' e - algebraMap κ' F' c) :=
            by
        rw [map_sub, AlgEquiv.commutes]; ring
      rw [hrw]
      exact sub_mem (nstab _ hc) hc
    rw [hσ, ← map_sub] at key
    rw [ValuationSubring.mem_nonunits_iff_or] at key ⊢
    rcases key with h0 | h
    · exact Or.inl ((map_eq_zero _).mp h0)
    · right
      rw [mem_iff, map_inv₀]
      exact h
end AlgebraicCurves.Places.Proofs.Place_smul_eq_and_sub_mem_nonunits_of_smul_eq_of_comap_eq
end ProofImplementation

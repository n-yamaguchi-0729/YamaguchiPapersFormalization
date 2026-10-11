/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Subgroup Is Arithmetic exists nat mem strict Periods conj
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj

open Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups Pointwise

noncomputable section

theorem _root_.Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj (𝒢 : Subgroup (GL (Fin 2)
  ℝ)) [𝒢.IsArithmetic] : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct
  (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods := by
  have : (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex := Subgroup.IsArithmetic.finiteIndex_comap 𝒢
  set Λ : Subgroup SL(2, ℤ) := (𝒢.comap (mapGL (R := ℤ) ℝ)).normalCore with hΛ
  have : Λ.FiniteIndex := inferInstance
  have hN : Λ.Normal := inferInstance
  refine ⟨Λ.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun γ ↦ ?_⟩
  have hT : ModularGroup.T ^ Λ.index ∈ Λ := Λ.pow_index_mem ModularGroup.T
  have hconj : γ⁻¹ * ModularGroup.T ^ Λ.index * γ ∈ 𝒢.comap (mapGL ℝ) := by
    apply Subgroup.normalCore_le
    simpa using hN.conj_mem _ hT γ⁻¹
  have hU : ∀ m : ℤ, Matrix.GeneralLinearGroup.upperRightHom ((m : ℝ)) =
      mapGL ℝ (ModularGroup.T ^ m) := by
    intro m
    simp only [Units.ext_iff, mapGL_coe_matrix, map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]
  have hU' := hU Λ.index
  rw [zpow_natCast, Int.cast_natCast] at hU'
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv,
    toConjAct_smul, inv_inv, hU', ← map_inv, ← map_mul, ← map_mul]
  exact hconj
end
end Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

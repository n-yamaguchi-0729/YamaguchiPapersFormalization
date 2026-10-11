/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.Valuation.RankOne

/-!
# Valued is Closed submodule of finite Dimensional of is Closed subfield
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield

theorem _root_.Valued.isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
      [CompleteSpace K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (K₀' : Subfield K) (hcl : IsClosed (K₀' : Set K)) (hnt : ∃ x ∈ K₀', x ≠ 0 ∧ Valued.v x < 1)
    (V : Submodule ↥K₀' K) [FiniteDimensional ↥K₀' ↥V] :
    IsClosed (V : Set K) := by
  classical
  obtain ⟨x₀, hx₀K, hx₀0, hx₀1⟩ := hnt
  have hnt' : (Valued.v : Valuation K Γ₀).IsNontrivial := ⟨⟨x₀, (map_ne_zero _).mpr hx₀0, hx₀1.ne⟩⟩
  have hMA : MulArchimedean (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v :
    Valuation K Γ₀))) := by
    refine ⟨fun a b hb => ?_⟩
    obtain ⟨xa, rfl⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation K Γ₀)) a
    obtain ⟨xb, rfl⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation K Γ₀)) b
    rw [Valuation.ofClass_eq_toMonoidWithZeroHom (Valued.v : Valuation K Γ₀)] at hb ⊢
    rw [← Valuation.restrict_def] at hb ⊢
    have hb1 : 1 < Valued.v xb := by
      by_contra h
      exact absurd hb (not_lt.mpr ((Valuation.restrict_le_one_iff _).mpr (not_lt.mp h)))
    have hxb0 : xb ≠ 0 := fun h => by rw [h, map_zero] at hb1; exact absurd hb1 (not_lt.mpr zero_le)
    rcases eq_or_ne (Valued.v xa) 0 with ha0 | ha0
    · refine ⟨0, ?_⟩
      rw [pow_zero]
      exact (Valuation.restrict_le_one_iff _).mpr (by rw [ha0]; exact zero_le)
    · have hxa0 : xa ≠ 0 := fun h => ha0 (by rw [h, map_zero])
      have h1 : Valued.v xb⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hb1
      obtain ⟨n, hn⟩ := hrk xb⁻¹ xa⁻¹ h1 (inv_ne_zero hxa0)
      refine ⟨n, ?_⟩
      rw [map_inv₀, map_inv₀, inv_pow] at hn
      have key : (Valued.v : Valuation K Γ₀).restrict xa ≤ (Valued.v : Valuation K Γ₀).restrict (xb
        ^ n) := by
        rw [Valuation.restrict_le_iff, map_pow]
        exact (inv_le_inv₀ (pow_pos (zero_lt_iff.mpr ((map_ne_zero _).mpr hxb0)) n)
          (zero_lt_iff.mpr ha0)).mp hn
      exact key.trans_eq (map_pow _ _ _)
  have hcs : CompleteSpace ↥K₀' := hcl.completeSpace_coe
  let hRO : Valuation.RankOne (Valued.v : Valuation K Γ₀) :=
    (Valuation.nonempty_rankOne_iff_mulArchimedean.mpr hMA).some
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K Γ₀
  let hK₀ : NormedField ↥K₀' := NormedField.induced ↥K₀' K K₀'.subtype Subtype.val_injective
  have hnorm : ∀ x : ↥K₀', ‖x‖ = ‖(x : K)‖ := fun x => rfl
  let : NontriviallyNormedField ↥K₀' := NontriviallyNormedField.ofNormNeOne
    ⟨⟨x₀, hx₀K⟩, fun h => hx₀0 (congrArg Subtype.val h), by
      rw [hnorm]; exact (Valued.toNormedField.norm_lt_one_iff.mpr hx₀1).ne⟩
  have hcsm : ContinuousSMul ↥K₀' K :=
    ⟨(continuous_subtype_val.comp continuous_fst).mul continuous_snd⟩
  exact @Submodule.closed_of_finiteDimensional ↥K₀' K _ hcs _ _ _ _ hcsm _ V _
end Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation

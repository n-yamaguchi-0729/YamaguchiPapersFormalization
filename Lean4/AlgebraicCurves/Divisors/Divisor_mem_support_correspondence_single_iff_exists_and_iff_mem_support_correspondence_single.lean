/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Divisors.Divisor_correspondence_single
import AlgebraicCurves.Places.Place_inertiaDeg_pos_of_finiteDimensional

/-!
# Divisor mem support correspondence single iff exists and iff mem support correspondence
single
-/

section ProofImplementation

namespace AlgebraicCurve.Divisor

open _root_.AlgebraicCurve

theorem mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
      [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ) (P Q : Place K F) :
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q) ∧
    (Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support) := by
  have key : ∀ (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
      (hfψ : FiniteAlong K ψ) (P Q : Place K F),
      Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support ↔
        ∃ R : Place K F', R.restrictAlong φ hφ = P ∧ R.restrictAlong ψ hψ = Q := by
    intro φ ψ hφ hψ hfψ P Q
    classical
    have he : ∀ R : Place K F', 0 < R.ramificationIndexAlong φ := fun R => by
      let := algebraAlong φ
      have := isIntegral_along φ hφ
      exact R.ramificationIndex_pos
    have hf : ∀ R : Place K F', 0 < R.inertiaDegAlong ψ hψ := fun R => by
      let := algebraAlong ψ
      have := isScalarTower_along ψ
      have : Module.Finite F F' := hfψ
      exact AlgebraicCurve.Place.inertiaDeg_pos_of_finiteDimensional R
    rw [Finsupp.mem_support_iff, AlgebraicCurve.Divisor.correspondence_single,
      Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [Finsupp.single_apply, one_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    constructor
    · intro h
      obtain ⟨R, hR, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      rw [Finset.mem_filter, Place.mem_fiberAlong] at hR
      exact ⟨R, hR.1, hR.2⟩
    · rintro ⟨R, hRφ, hRψ⟩
      apply ne_of_gt
      apply Finset.sum_pos'
      · intro i _
        positivity
      · refine ⟨R, ?_, ?_⟩
        · rw [Finset.mem_filter, Place.mem_fiberAlong]; exact ⟨hRφ, hRψ⟩
        · exact mul_pos (Int.natCast_pos.mpr (he R)) (Int.natCast_pos.mpr (hf R))
  refine ⟨key φ ψ hφ hψ hfψ P Q, ?_⟩
  rw [key φ ψ hφ hψ hfψ P Q, key ψ φ hψ hφ hfφ Q P]
  exact ⟨fun ⟨R, h1, h2⟩ => ⟨R, h2, h1⟩, fun ⟨R, h1, h2⟩ => ⟨R, h2, h1⟩⟩
end AlgebraicCurve.Divisor
end ProofImplementation

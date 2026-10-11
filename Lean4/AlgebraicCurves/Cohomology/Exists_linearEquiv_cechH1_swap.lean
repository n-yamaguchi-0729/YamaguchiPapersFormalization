/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_cechH1_swap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Cech.DivisorSections

/-!
# Exists linear Equiv cech H1 swap
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Exists_linearEquiv_cechH1_swap

universe u v

theorem _root_.AlgebraicCurve.exists_linearEquiv_cechH1_swap
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    (S S' : Set (AlgebraicCurve.Place K F)) (D : AlgebraicCurve.Divisor K F) :
    ∃ e : AlgebraicCurve.cechH1 S S' D ≃ₗ[K] AlgebraicCurve.cechH1 S' S D,
      ∀ (f : F) (h : f ∈ AlgebraicCurve.lSpaceOn (S ∩ S') D) (h' : f ∈ AlgebraicCurve.lSpaceOn (S'
        ∩ S) D),
        e (Submodule.Quotient.mk ⟨f, h⟩) = Submodule.Quotient.mk ⟨f, h'⟩ := by
  have hinter : AlgebraicCurve.lSpaceOn (S ∩ S') D = AlgebraicCurve.lSpaceOn (S' ∩ S) D := by rw
    [Set.inter_comm]
  let e₀ : ↥(AlgebraicCurve.lSpaceOn (S ∩ S') D) ≃ₗ[K] ↥(AlgebraicCurve.lSpaceOn (S' ∩ S) D) :=
    LinearEquiv.ofEq _ _ hinter
  have he₀ : ∀ g : ↥(AlgebraicCurve.lSpaceOn (S ∩ S') D), ((e₀ g : ↥(AlgebraicCurve.lSpaceOn (S' ∩
    S) D)) : F) = g :=
    fun g => rfl
  have hmap : (LinearMap.range (AlgebraicCurve.cechDiff S S' D)).map (e₀ : _ →ₗ[K] _) =
      LinearMap.range (AlgebraicCurve.cechDiff S' S D) := by
    ext g
    rw [AlgebraicCurve.mem_range_cechDiff_iff, Submodule.mem_map]
    constructor
    · rintro ⟨g', hg', rfl⟩
      rw [LinearEquiv.coe_coe, he₀, sup_comm]
      exact (AlgebraicCurve.mem_range_cechDiff_iff g').mp hg'
    · intro hg
      refine ⟨e₀.symm g, ?_, by simp⟩
      rw [AlgebraicCurve.mem_range_cechDiff_iff, sup_comm]
      exact hg
  refine ⟨Submodule.Quotient.equiv _ _ e₀ hmap, fun f h h' => ?_⟩
  rw [Submodule.Quotient.equiv_apply]
  rfl
end AlgebraicCurves.Cohomology.Proofs.Exists_linearEquiv_cechH1_swap
end ProofImplementation

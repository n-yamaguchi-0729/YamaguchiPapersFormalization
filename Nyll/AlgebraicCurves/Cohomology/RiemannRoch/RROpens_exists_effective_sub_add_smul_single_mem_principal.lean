/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
# RROpens exists effective sub add smul single mem principal
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RROpensExistsEffectiveSubAddSmul

universe u v

open AlgebraicCurve Module

theorem _root_.AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal {K : Type
  u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] (g : ℕ) (Kc : Divisor K F)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (hP : P.deg = 1) (A : Divisor K F) (hA : Divisor.degree A = 0) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧
      E - (A + (g : ℤ) • Finsupp.single P 1) ∈ Divisor.principal (K := K) (F := F) := by
  set D : Divisor K F := A + (g : ℤ) • Finsupp.single P 1 with hD
  have hdeg : Divisor.degree D = g := by
    rw [hD, map_add, map_zsmul, Divisor.degree_single, hA, hP]
    simp
  have hpos : 0 < finrank K (LSpace D) := by
    have h := hRR D
    rw [hdeg] at h
    have h0 : (0 : ℤ) ≤ (ell (Kc - D) : ℤ) := Int.natCast_nonneg _
    have h1 : (1 : ℤ) ≤ (ell D : ℤ) := by linarith
    have h2 : 1 ≤ ell D := by exact_mod_cast h1
    exact h2
  have hne : LSpace D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨f, hfD, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hord : ∀ v : Place K F, -D v ≤ v.ord f := (mem_lSpace_iff_ord.mp hfD).resolve_left hf0
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine ⟨D + Df, fun v => ?_, ?_⟩
  · rw [Finsupp.add_apply, hDf v]
    linarith [hord v]
  · rw [add_sub_cancel_left]
    exact ⟨f, hf0, hDf⟩

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RROpensExistsEffectiveSubAddSmul
end ProofImplementation

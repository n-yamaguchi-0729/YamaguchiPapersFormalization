/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ

/-!
# Exists flag Adapted Basis At l Space nsmul pole Divisor
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FlagAdaptedPoleBasis

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1) (M₁ : ℕ) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ σ, e σ ≤ M₁) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) ∧
      (∀ M ≤ M₁, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      (∀ M ≤ M₁, LinearIndependent K
        (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) := by
  classical
  induction M₁ with
  | zero =>
    have : FiniteDimensional K ↥(LSpace (0 • D) : Submodule K F) := hFD 0
    have hfr0 : Module.finrank K ↥(LSpace (0 • D) : Submodule K F) = 1 := by
      have h : ell ((0:ℕ) • D) = 1 := by rw [zero_smul]; exact hell0
      exact h
    have hne : (LSpace (0 • D) : Submodule K F) ≠ ⊥ := by
      intro h; rw [h] at hfr0; simp at hfr0
    obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hLv : (LSpace (0 • D) : Submodule K F) = Submodule.span K {v} := by
      refine (Submodule.eq_of_le_of_finrank_le
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvmem))
        (by rw [finrank_span_singleton hvne, hfr0])).symm
    refine ⟨1, fun _ => v, fun _ => 0, fun _ => le_refl 0, ?_, ?_, ?_⟩
    · intro σ; simpa using hvmem
    · intro M hM; obtain rfl : M = 0 := Nat.le_zero.mp hM
      rw [hLv]; refine Submodule.span_mono ?_
      rintro w rfl; exact ⟨0, 0, le_refl 0, by simp⟩
    · intro M hM; obtain rfl : M = 0 := Nat.le_zero.mp hM
      let hU : Unique {p : Fin 1 × ℕ // p.2 + (fun _ => 0) p.1 ≤ 0} :=
        ⟨⟨⟨(0, 0), by simp⟩⟩, by
          rintro ⟨⟨a, j⟩, ha⟩; simp only [add_zero] at ha
          exact Subtype.ext (Prod.ext (Subsingleton.elim a 0) (Nat.le_zero.mp ha))⟩
      refine linearIndependent_unique_iff.mpr ?_
      have : (default : {p : Fin 1 × ℕ // p.2 + (fun _ => 0) p.1 ≤ 0}).val.2 = 0 := rfl
      simp only [this, pow_zero, one_mul]
      exact hvne
  | succ M₁ ih =>
    obtain ⟨d', y, e, hle', hy', hspan', hLI'⟩ := ih
    exact exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor_succ
      x hx D hD hFD hell0 M₁ y e hle' hy' hspan' hLI'
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.FlagAdaptedPoleBasis
end ProofImplementation

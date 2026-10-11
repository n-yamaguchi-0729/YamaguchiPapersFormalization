/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
import AlgebraicCurves.Cohomology.RiemannRoch.LSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
import AlgebraicCurves.FunctionFields.LinearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq

/-!
# Exists flag Adapted Basis l Space nsmul pole Divisor
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsFlagAdaptedBasisLSpace

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1)
    (M₀ d g₀ : ℕ) (_hd : 1 ≤ d)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ M : ℕ, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      LinearIndependent K (fun p : Fin d' × ℕ => x ^ p.2 * y p.1) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) := by
  obtain ⟨d', y, e, hle, hy, hspanFin, hLIat⟩ :=
    exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor x hx D hD hFD hell0 (M₀ + 1)
  have hspanAll : ∀ M : ℕ, (LSpace (M • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ} := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M ih =>
      rcases le_or_gt M (M₀ + 1) with hM | hM
      · exact hspanFin M hM
      · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
        have hstep := lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
          x D hD hFD M₀ d g₀ hell M' (by omega)
        refine hstep.trans (sup_le ((ih M' (by omega)).trans (Submodule.span_mono ?_)) ?_)
        · rintro z ⟨σ, j, hje, rfl⟩; exact ⟨σ, j, by omega, rfl⟩
        · rw [Submodule.map_le_iff_le_comap]
          refine (ih M' (by omega)).trans (Submodule.span_le.mpr ?_)
          rintro z ⟨σ, j, hje, rfl⟩
          exact Submodule.mem_comap.mpr (Submodule.subset_span
            ⟨σ, j + 1, by omega, by simp [LinearMap.mulLeft_apply, ← mul_assoc, ← pow_succ']⟩)
  exact ⟨d', y, e, hspanAll,
    linearIndependent_pow_mul_of_flagAdaptedBasisAt_of_ell_eq
      x D hD hFD M₀ d g₀ hell y e hle hy hspanAll hLIat,
    hy⟩
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsFlagAdaptedBasisLSpace
end ProofImplementation

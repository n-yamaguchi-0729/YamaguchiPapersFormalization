/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver

/-!
# Exists D ne zero
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.Exists_D_ne_zero

theorem _root_.AlgebraicCurve.exists_D_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hbot : Submodule.span F (Set.range (KaehlerDifferential.D K F)) = ⊥ :=
    Submodule.span_eq_bot.2 (by rintro _ ⟨t, rfl⟩; exact h t)
  rw [hbot, Submodule.mem_bot] at hmem
  exact hω hmem
end AlgebraicCurves.Geometry.Proofs.Exists_D_ne_zero
end ProofImplementation

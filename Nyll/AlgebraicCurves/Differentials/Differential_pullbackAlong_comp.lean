/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Differential_pullbackAlong_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Differentials.Maps

/-!
# Differential pullback Along comp
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Differential_pullbackAlong_comp

open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential

theorem _root_.AlgebraicCurve.Differential.pullbackAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F']
      [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (ψ.comp φ) ω =
      AlgebraicCurve.Differential.pullbackAlong ψ (AlgebraicCurve.Differential.pullbackAlong φ ω)
        := by
  have key : ∀ ω ∈ Submodule.span F (Set.range (D K F)),
      pullbackAlong (ψ.comp φ) ω = pullbackAlong ψ (pullbackAlong φ ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      rw [pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, AlgHom.comp_apply]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
    | smul a x _ hx =>
        rw [pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, hx, AlgHom.comp_apply]
  exact key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial)
end AlgebraicCurves.Differentials.Proofs.Differential_pullbackAlong_comp
end ProofImplementation

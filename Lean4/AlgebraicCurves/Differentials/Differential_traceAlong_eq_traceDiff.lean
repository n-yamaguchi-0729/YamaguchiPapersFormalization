/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Differential_traceAlong_eq_traceDiff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Differentials.Trace
import AlgebraicCurves.Differentials.TraceDiff_apply

/-!
# Differential trace Along eq trace Diff
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Differential_traceAlong_eq_traceDiff

open AlgebraicCurve KaehlerDifferential TensorProduct

theorem _root_.AlgebraicCurve.Differential.traceAlong_eq_traceDiff
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (h : AlgebraicCurve.SeparableAlong K φ) (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.traceAlong φ η =
      (letI := AlgebraicCurve.algebraAlong φ
       haveI := AlgebraicCurve.isScalarTower_along φ
       AlgebraicCurve.traceDiff K F F' η) := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Algebra.IsSeparable F F' := h
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
  induction t using TensorProduct.inductionOn with
  | tmul y ω =>
    have he : KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F' (y ⊗ₜ ω) =
        y • Differential.pullbackAlong φ ω := by
      rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [he, Differential.traceAlong_smul_pullbackAlong φ h y ω]
    change Algebra.trace F F' y • ω = traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω)
    rw [traceDiff_apply]
  | add s t hs ht =>
    rw [map_add, map_add, map_add, hs, ht]
end AlgebraicCurves.Differentials.Proofs.Differential_traceAlong_eq_traceDiff
end ProofImplementation

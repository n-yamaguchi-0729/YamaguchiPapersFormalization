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

import AlgebraicCurves.Divisors.Correspondences

/-!
# Place one le ramification Index Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_one_le_ramificationIndexAlong

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w := by
  let := AlgebraicCurve.algebraAlong φ
  have := AlgebraicCurve.isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem _root_.AlgebraicCurve.Place.one_le_ramificationIndexAlong {K F F' : Type*} [Field K] [Field
  F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w :
  AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w :=
  AlgebraicCurve.Place.solution_impl φ hφ w
end AlgebraicCurves.Places.Proofs.Place_one_le_ramificationIndexAlong
end ProofImplementation

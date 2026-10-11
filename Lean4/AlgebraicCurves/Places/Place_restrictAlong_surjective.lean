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
import AlgebraicCurves.Places.Place_exists_restrict_eq

/-!
# Place restrict Along surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_surjective

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrictAlong_surjective
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong K φ) (hsep : AlgebraicCurve.SeparableAlong K φ) :
    Function.Surjective (fun w : AlgebraicCurve.Place K F' => w.restrictAlong φ hφ) := by
  intro v
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  obtain ⟨W, hW⟩ := AlgebraicCurve.Place.exists_restrict_eq (K := K) (F' := F) (M := F') v
  exact ⟨W, hW⟩
end AlgebraicCurves.Places.Proofs.Place_restrictAlong_surjective
end ProofImplementation

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
import AlgebraicCurves.FunctionFields.CurveOver

/-!
# Place inertia Deg Along eq one of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_inertiaDegAlong_eq_one_of_isAlgClosed

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.inertiaDegAlong_eq_one_of_isAlgClosed
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (W : Place K F') :
    W.inertiaDegAlong ψ hψ = 1 := by
  let := algebraAlong ψ
  have := isScalarTower_along ψ
  have := isIntegral_along ψ hψ
  have h := W.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h
end AlgebraicCurves.Places.Proofs.Place_inertiaDegAlong_eq_one_of_isAlgClosed
end ProofImplementation

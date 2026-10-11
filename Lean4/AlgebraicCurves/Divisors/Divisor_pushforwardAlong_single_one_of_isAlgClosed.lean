/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardAlong_single_one_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Places.Place_module_finite_residueField_restrict

/-!
# Divisor pushforward Along single one of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_single_one_of_isAlgClosed

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_single_one_of_isAlgClosed
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.IsCurveOver K F]
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (W : AlgebraicCurve.Place K F') :
    AlgebraicCurve.Divisor.pushforwardAlong ψ hψ (Finsupp.single W 1) =
      Finsupp.single (W.restrictAlong ψ hψ) 1 := by
  let := algebraAlong ψ
  have := isScalarTower_along ψ
  have := isIntegral_along ψ hψ
  have : Module.Finite F F' := hfin
  have := AlgebraicCurve.Place.module_finite_residueField_restrict K F F' W
  have := IsCurveOver.finiteResidue (K := K) (W.restrict F)
  have : Module.Finite K W.ResidueField := Module.Finite.trans (W.restrict F).ResidueField _
  have hW : W.deg = 1 := W.deg_eq_one_of_isAlgClosed_of_finite
  have hV : (W.restrictAlong ψ hψ).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
  have h1 : W.inertiaDegAlong ψ hψ = 1 := by
    have ht : (W.restrictAlong ψ hψ).deg * W.inertiaDegAlong ψ hψ = W.deg :=
      W.deg_restrict_mul_inertiaDeg (F := F)
    rw [hV, hW, one_mul] at ht
    exact ht
  rw [Divisor.pushforwardAlong_single, h1, Nat.cast_one, mul_one]
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_single_one_of_isAlgClosed
end ProofImplementation

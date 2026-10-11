/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pushforward_smul

/-!
# Semilinear Aut pushforward Along smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pushforwardAlong_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g :
  SemilinearAut K F} {g' : SemilinearAut K F'} (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg'
  : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F') : Divisor.pushforwardAlong φ hφ (g' • D)
  = g • Divisor.pushforwardAlong φ hφ D := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact pushforward_smul hgg' D

end

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pushforwardAlong_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.pushforwardAlong_smul {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (φ : F
  →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K
  F') : Divisor.pushforwardAlong φ hφ (g' • D) = g • Divisor.pushforwardAlong φ hφ D := by
  exact
    _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pushforwardAlong_smul.solution
    (K := K) (F := F) (F' := F') (g := g) (g' := g') (φ := φ) (hφ := hφ) (hgg' := hgg') (D := D)

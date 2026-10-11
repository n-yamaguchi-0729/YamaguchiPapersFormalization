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

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Separable Along of char Zero
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.SeparableAlong_of_charZero

open AlgebraicCurve

theorem _root_.AlgebraicCurve.separableAlong_of_charZero {K F F₁ : Type*} [Field K] [Field F]
  [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ :
  φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  let := algebraAlong φ
  have := isIntegral_along φ hφ
  exact Algebra.IsSeparable.of_integral F F₁
end AlgebraicCurves.FunctionFields.Proofs.SeparableAlong_of_charZero
end ProofImplementation

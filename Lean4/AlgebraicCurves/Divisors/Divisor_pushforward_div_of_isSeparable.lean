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

import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Divisors.Divisor_pushforwardNormFormula_of_isSeparable

/-!
# Divisor pushforward div of is Separable
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforward_div_of_isSeparable

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.pushforward_div_of_isSeparable {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f
  ≠ 0) {D : Divisor K F'} (hD : ∀ w, D w = w.ord f) {E : Divisor K F} (hE : ∀ v, E v = v.ord
  (Algebra.norm F f)) : Divisor.pushforward F D = E :=
  pushforward_eq_of_normFormula AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable hf hD
    hE
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforward_div_of_isSeparable
end ProofImplementation

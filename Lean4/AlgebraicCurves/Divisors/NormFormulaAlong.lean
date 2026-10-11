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
import AlgebraicCurves.Divisors.Divisor_pushforwardNormFormula

/-!
# Norm Formula Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.NormFormulaAlong

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.normFormulaAlong {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [CharZero F] (φ : F →ₐ[K] F') [HasPrincipalDivisors K F'] (hfin :
  FiniteAlong K φ) (hsep : SeparableAlong K φ) : NormFormulaAlong K φ hfin := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  exact Divisor.pushforwardNormFormula

end
end AlgebraicCurves.Divisors.Proofs.NormFormulaAlong
end ProofImplementation

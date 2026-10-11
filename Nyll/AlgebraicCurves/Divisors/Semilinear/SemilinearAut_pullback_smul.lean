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
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_restrict_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ramificationIndex_smul

/-!
# Semilinear Aut pullback smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pullback_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' :
  SemilinearAut K F'} [HasPrincipalDivisors K F'] (hgg' : IntertwinesAlong (algebraMap F F') g g')
  (D : Divisor K F) : Divisor.pullback F' (g • D) = g' • Divisor.pullback F' D := by
  ext w
  rw [Divisor.pullback_apply, divisor_smul_apply, divisor_smul_apply, Divisor.pullback_apply,
    restrict_smul hgg'.inv w, ramificationIndex_smul hgg'.inv w]

end

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pullback_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.pullback_smul {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g :
  SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (hgg' : IntertwinesAlong
  (algebraMap F F') g g') (D : Divisor K F) : Divisor.pullback F' (g • D) = g' • Divisor.pullback
  F' D := by
  exact _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pullback_smul.solution (K
    := K) (F := F) (F' := F') (g := g) (g' := g') (hgg' := hgg') (D := D)

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
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_restrict_smul
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_inertiaDeg_smul

/-!
# Semilinear Aut pushforward smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pushforward_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' :
  SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') :
  Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [smul_single, Divisor.pushforward_single, Divisor.pushforward_single, smul_single,
      restrict_smul hgg' w, inertiaDeg_smul hgg' w]

end

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pushforward_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.pushforward_smul {K F F' : Type*} [Field K] [Field F] [Field
  F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
  {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g
  g') (D : Divisor K F') : Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by
  exact _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pushforward_smul.solution
    (K := K) (F := F) (F' := F') (g := g) (g' := g') (hgg' := hgg') (D := D)

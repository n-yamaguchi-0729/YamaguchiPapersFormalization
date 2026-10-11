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

/-!
# Semilinear Aut ord algebra Map smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ord_algebraMap_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong
  (algebraMap F F') g g') (w : Place K F') (f : F) : (g' • w).ord (algebraMap F F' f) = w.ord
  (algebraMap F F' (g⁻¹ • f)) := by
  have hrw : algebraMap F F' f = g' • (algebraMap F F' (g⁻¹ • f)) := by
    rw [hgg' (g⁻¹ • f), smul_inv_smul]
  rw [hrw]
  exact ord_smul g' w _

end

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ord_algebraMap_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.ord_algebraMap_smul {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' :
  SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) :
  (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by
  exact
    _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ord_algebraMap_smul.solution (K
    := K) (F := F) (F' := F') (g := g) (g' := g') (hgg' := hgg') (w := w) (f := f)

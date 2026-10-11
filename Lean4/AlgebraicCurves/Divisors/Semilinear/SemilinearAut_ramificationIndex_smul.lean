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
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ord_algebraMap_smul

/-!
# Semilinear Aut ramification Index smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ramificationIndex_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong
  (algebraMap F F') g g') (w : Place K F') : (g' • w).ramificationIndex F = w.ramificationIndex F
  := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    exact ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], by rw [← ord_algebraMap_smul hgg', hford]⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    rw [ord_algebraMap_smul hgg', inv_smul_smul, hford]

end

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ramificationIndex_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.ramificationIndex_smul {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' :
  SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' •
  w).ramificationIndex F = w.ramificationIndex F := by
  exact
    _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ramificationIndex_smul.solution
    (K := K) (F := F) (F' := F') (g := g) (g' := g') (hgg' := hgg') (w := w)

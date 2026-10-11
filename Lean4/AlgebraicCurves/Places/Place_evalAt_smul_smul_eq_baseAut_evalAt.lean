/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Divisors.Semilinear
import AlgebraicCurves.Places.Evaluation

/-!
# Place eval At smul smul eq base Aut eval At
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_smul_smul_eq_baseAut_evalAt

open AlgebraicCurve IsLocalRing

theorem _root_.AlgebraicCurve.Place.evalAt_smul_smul_eq_baseAut_evalAt
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : SemilinearAut K F) (v : AlgebraicCurve.Place K F)
    (hv : v.IsRational) (hσv : (σ • v).IsRational) (f : F) :
    (σ • v).evalAt (σ • f) = SemilinearAut.baseAut σ (v.evalAt f) := by
  classical
  by_cases hf : f ∈ v.toValuationSubring
  · have hσf : σ • f ∈ (σ • v).toValuationSubring := by
      rw [SemilinearAut.smul_toValuationSubring]
      exact ValuationSubring.smul_mem_pointwise_smul σ f v.toValuationSubring hf
    apply (σ • v).algebraMap_residueField_injective
    rw [(σ • v).algebraMap_evalAt hσv hσf, ← SemilinearAut.smulResidueRingEquiv_algebraMap σ v,
      v.algebraMap_evalAt hv hf]
    change residue _ _ = IsLocalRing.ResidueField.mapEquiv _ (residue _ _)
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  · have hσf : σ • f ∉ (σ • v).toValuationSubring := by
      rw [SemilinearAut.smul_toValuationSubring,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hf
    rw [Place.evalAt, Place.evalAt, dite_eq_right hσf, dite_eq_right hf, map_zero]
end AlgebraicCurves.Places.Proofs.Place_evalAt_smul_smul_eq_baseAut_evalAt
end ProofImplementation

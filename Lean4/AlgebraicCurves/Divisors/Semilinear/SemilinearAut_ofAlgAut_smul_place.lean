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

import AlgebraicCurves.Divisors.Semilinear

/-!
# Semilinear Aut of Alg Aut smul place
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ofAlgAut_smul_place

open scoped Pointwise

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v :
  AlgebraicCurve.Place K F) : AlgebraicCurve.SemilinearAut.ofAlgAut σ • v = σ • v := by
  have hfun : ∀ x : F, AlgebraicCurve.SemilinearAut.ofAlgAut σ • x = σ • x := fun _ => rfl
  apply AlgebraicCurve.Place.toValuationSubring_injective
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring,
    AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  simp only [hfun]

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ofAlgAut_smul_place
end ProofImplementation


open AlgebraicCurve
theorem AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place {K F : Type*} [Field K] [Field F] [Algebra
  K F] (σ : F ≃ₐ[K] F) (v : Place K F) : ofAlgAut σ • v = σ • v := by
  exact
    _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_ofAlgAut_smul_place.solution (K
    := K) (F := F) (σ := σ) (v := v)

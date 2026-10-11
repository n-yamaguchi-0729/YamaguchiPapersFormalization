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

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Semilinear

/-!
# Place restrict Along alg Equiv eq of Alg Aut symm smul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul

open AlgebraicCurve
open scoped Pointwise

theorem _root_.AlgebraicCurve.Place.restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (v : Place K F) :
    v.restrictAlong σ.toAlgHom hσ = SemilinearAut.ofAlgAut σ.symm • v := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  change σ x ∈ v.toValuationSubring ↔ _
  rfl

end AlgebraicCurves.Places.Proofs.Place_restrictAlong_algEquiv_eq_ofAlgAut_symm_smul
end ProofImplementation

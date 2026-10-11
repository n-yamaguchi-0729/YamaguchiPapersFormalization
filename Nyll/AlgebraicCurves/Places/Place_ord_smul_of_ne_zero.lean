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

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Place ord smul of ne zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_smul_of_ne_zero

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ord_smul_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra
  K F] (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [smul_zero]
  · have halg : algebraMap K F c ≠ 0 :=
      fun h => hc ((algebraMap K F).injective (by rw [h, map_zero]))
    have hunit : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩, ?_⟩
      ext
      simp [mul_inv_cancel₀ halg]
    have h0 : v.ord (algebraMap K F c) = 0 := by
      have h1 : v.adicValuation (algebraMap K F c) = 1 :=
        (v.adicValuation_coe_eq_one_iff ⟨algebraMap K F c, v.algebraMap_mem' c⟩).mpr hunit
      simp [AlgebraicCurve.Place.ord, h1]
    rw [Algebra.smul_def, v.ord_mul halg hx0, h0, zero_add]
end AlgebraicCurves.Places.Proofs.Place_ord_smul_of_ne_zero
end ProofImplementation

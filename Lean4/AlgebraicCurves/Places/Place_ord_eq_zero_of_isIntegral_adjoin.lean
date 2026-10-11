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

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Place_mem_toValuationSubring_of_isIntegral_adjoin

/-!
# Place ord eq zero of is Integral adjoin
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_eq_zero_of_isIntegral_adjoin

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_isIntegral_adjoin {K F : Type*} [Field K] [Field
  F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral
  (Algebra.adjoin K {j}) x) (hx' : IsIntegral (Algebra.adjoin K {j}) x⁻¹) : v.ord x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact v.ord_zero
  · have hxa : x ∈ v.toValuationSubring :=
      v.mem_toValuationSubring_of_isIntegral_adjoin hj hx
    have hxi : x⁻¹ ∈ v.toValuationSubring :=
      v.mem_toValuationSubring_of_isIntegral_adjoin hj hx'
    have hunit : IsUnit (⟨x, hxa⟩ : v.toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hxi⟩, ?_⟩
      ext
      simp [mul_inv_cancel₀ hx0]
    have h1 : v.adicValuation x = 1 :=
      (v.adicValuation_coe_eq_one_iff ⟨x, hxa⟩).mpr hunit
    simp [AlgebraicCurve.Place.ord, h1]
end AlgebraicCurves.Places.Proofs.Place_ord_eq_zero_of_isIntegral_adjoin
end ProofImplementation

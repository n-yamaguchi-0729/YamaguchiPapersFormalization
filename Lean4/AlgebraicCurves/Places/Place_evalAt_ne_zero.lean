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

import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Places.Place_mem_of_ord_nonneg

/-!
# Place evalAt ne zero

A nonzero function of order zero has nonzero evaluation at a rational place.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_ne_zero

open IsLocalRing AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.evalAt_ne_zero {K F : Type*} [Field K] [Field F]
  [Algebra K F] (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
  v.evalAt f ≠ 0 := by
  have hmem : f ∈ v.toValuationSubring := v.mem_of_ord_nonneg hf h.ge
  have hunit : IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    rw [h, zpow_zero, mul_one] at hu
    have huf : (⟨f, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [huf]
    exact u.isUnit
  have hres : residue v.toValuationSubring (⟨f, hmem⟩ : v.toValuationSubring) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr hunit
  intro h0
  have key := v.algebraMap_evalAt hv hmem
  rw [h0, map_zero] at key
  exact hres key.symm
end AlgebraicCurves.Places.Proofs.Place_evalAt_ne_zero
end ProofImplementation

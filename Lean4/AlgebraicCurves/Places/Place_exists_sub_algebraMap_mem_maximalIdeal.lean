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
import AlgebraicCurves.Places.Place_deg_eq_one_iff_surjective_algebraMap_residueField

/-!
# Place exists sub algebra Map mem maximal Ideal
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_sub_algebraMap_mem_maximalIdeal

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_sub_algebraMap_mem_maximalIdeal {K F : Type*} [Field K]
  [Field F]
    [Algebra K F] (u : AlgebraicCurve.Place K F) (hdeg : u.deg = 1) (b : u.toValuationSubring) :
    ∃ c : K, b - algebraMap K u.toValuationSubring c
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by
  obtain ⟨c, hc⟩ := ((Place.deg_eq_one_iff_surjective_algebraMap_residueField u).mp hdeg)
    (IsLocalRing.residue _ b)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero,
    IsScalarTower.algebraMap_apply K u.toValuationSubring u.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

end AlgebraicCurves.Places.Proofs.Place_exists_sub_algebraMap_mem_maximalIdeal
end ProofImplementation

attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id
  ModularCurve.coeffMap_single

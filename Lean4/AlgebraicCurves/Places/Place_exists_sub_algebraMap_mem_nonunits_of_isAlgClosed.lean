/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup

/-!
# Place exists sub algebra Map mem nonunits of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed

open AlgebraicCurve
open scoped Pointwise

theorem _root_.AlgebraicCurve.Place.exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
    {κ' : Type*} [Field κ'] [IsAlgClosed κ'] {F' : Type*} [Field F'] [Algebra κ' F']
    (P' : Place κ' F') [P'.FiniteResidue]
    (x : F') (hx : x ∈ P'.toValuationSubring) :
    ∃ c : κ', x - algebraMap κ' F' c ∈ P'.toValuationSubring.nonunits := by
  classical
  have : Module.Finite κ' P'.ResidueField := AlgebraicCurve.Place.FiniteResidue.finite
  have : Algebra.IsIntegral κ' P'.ResidueField := Algebra.IsIntegral.of_finite κ' _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ') (K :=
    P'.ResidueField)).2
    (IsLocalRing.residue _ ⟨x, hx⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨x, hx⟩ : P'.toValuationSubring) - algebraMap κ' P'.toValuationSubring c ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc,
      IsScalarTower.algebraMap_apply κ' P'.toValuationSubring P'.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq,
      sub_self]
  have e : ((⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c : P'.toValuationSubring) : F') = x -
    algebraMap κ' F' c := by
    change P'.toValuationSubring.subtype (⟨x, hx⟩ - algebraMap κ' P'.toValuationSubring c) = _
    rw [map_sub]
    rfl
  rw [← e]
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hmem
end AlgebraicCurves.Places.Proofs.Place_exists_sub_algebraMap_mem_nonunits_of_isAlgClosed
end ProofImplementation

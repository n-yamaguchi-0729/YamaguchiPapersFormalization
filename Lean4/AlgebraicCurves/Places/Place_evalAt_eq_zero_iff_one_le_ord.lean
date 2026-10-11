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

import AlgebraicCurves.Places.Evaluation

/-!
# Place eval At eq zero iff one le ord
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_eq_zero_iff_one_le_ord

open IsLocalRing AlgebraicCurve

private theorem ord_nonnegative_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : Place K F) {f : F} (hf : f ∈ x.toValuationSubring) : 0 ≤ x.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨uniformizer, hUniformizer⟩ :=
    IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  obtain ⟨n, unit, hFactorization⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : x.toValuationSubring))
      (by simpa [Subtype.ext_iff] using hf0) hUniformizer
  have hCoe :
      f = ((unit : x.toValuationSubring) : F) * ((uniformizer : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hFactorization
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hCoe, x.ord_unit_smul_zpow unit hUniformizer (n : ℤ)]
  exact Int.natCast_nonneg n

theorem _root_.AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord {K F : Type*} [Field K] [Field F]
  [Algebra K F]
    (x : Place K F) (hx : x.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ x.toValuationSubring) : x.evalAt f = 0 ↔ 1 ≤ x.ord f := by
  constructor
  · intro hEval
    have hMap := x.algebraMap_evalAt hx hf
    rw [hEval, map_zero] at hMap
    have hMaximal :
        (⟨f, hf⟩ : x.toValuationSubring) ∈ IsLocalRing.maximalIdeal x.toValuationSubring :=
      (IsLocalRing.residue_eq_zero_iff _).mp hMap.symm
    have hNonnegative : 0 ≤ x.ord f := ord_nonnegative_of_mem x hf
    have hPositive : 0 < x.ord f := by
      rcases lt_or_eq_of_le hNonnegative with hPositive | hZero
      · exact hPositive
      · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hMaximal
        exfalso
        apply hMaximal
        obtain ⟨uniformizer, hUniformizer⟩ :=
          IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
        obtain ⟨unit, hFactorization⟩ := x.exists_unit_mul_zpow hf0 hUniformizer
        rw [← hZero, zpow_zero, mul_one] at hFactorization
        have hSubtype : (⟨f, hf⟩ : x.toValuationSubring) = unit :=
          Subtype.ext hFactorization
        rw [hSubtype]
        exact unit.isUnit
    omega
  · intro hOrd
    have hMaximal :
        (⟨f, hf⟩ : x.toValuationSubring) ∈ IsLocalRing.maximalIdeal x.toValuationSubring :=
      by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hUnit
        obtain ⟨unit, hUnit⟩ := hUnit
        have hCoe : f = ((unit : x.toValuationSubring) : F) := by rw [hUnit]
        have hZero : x.ord f = 0 := by
          rw [hCoe]
          exact x.ord_coe_unit unit
        omega
    have hEval := x.algebraMap_evalAt hx hf
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hMaximal, map_eq_zero] at hEval
    exact hEval

end AlgebraicCurves.Places.Proofs.Place_evalAt_eq_zero_iff_one_le_ord
end ProofImplementation

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Evaluation

/-! # A nonzero place evaluation has order zero -/

noncomputable section

namespace AlgebraicCurve.Place

/-- Nonzero evaluation at a rational place detects an actual unit in its
valuation ring, and hence a function of order zero. -/
theorem ord_eq_zero_of_evalAt_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {f : F}
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  classical
  have hmem : f ∈ v.toValuationSubring := by
    by_contra hn
    exact h (by simp [evalAt, hn])
  have hres : IsLocalRing.residue v.toValuationSubring
      (⟨f, hmem⟩ : v.toValuationSubring) ≠ 0 := by
    intro hz
    have heval := v.algebraMap_evalAt hv hmem
    rw [hz] at heval
    exact h (v.algebraMap_residueField_injective
      (heval.trans (map_zero (algebraMap K v.ResidueField)).symm))
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have hcoe : f = ((u : v.toValuationSubring) : F) :=
    (congrArg Subtype.val hu).symm
  rw [hcoe]
  exact v.ord_coe_unit u

end AlgebraicCurve.Place

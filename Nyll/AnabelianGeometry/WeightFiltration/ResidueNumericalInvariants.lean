/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidueRanks
import Mathlib.Data.Nat.Log

/-!
# Recovering numerical invariants from the actual residue filtration

For an exponent greater than one, the kernel determines the genus and the
image determines the size of a nonempty boundary. These are explicit
numerical formulas. Recognition of the filtration from arithmetic group
data is a separate theorem and is not an assumption hidden in this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Algebra K F] [IsCurveOver K F]
  (M : CurveModel K F)
  (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
  (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

include ε

/-- The actual residue kernel determines the genus. -/
theorem genus_eq_log_card_finiteResidue_ker (hn₁ : 1 < (n : ℕ)) :
    genusFF K F = Nat.log (n : ℕ)
      (Nat.card (finiteResidue M n j hj hn xi).ker) / 2 := by
  rw [natCard_finiteResidue_ker M ε n j hj hn xi, Nat.log_pow hn₁]
  omega

variable [Fintype (M.openBoundaryPlaces j)]

omit [CharZero K] in
/-- For nonempty boundary, its cardinality is one plus the logarithm of the
actual residue-image cardinality. The empty boundary is excluded explicitly. -/
theorem boundaryCard_eq_log_card_finiteResidue_range
    (v₀ : M.openBoundaryPlaces j) (hn₁ : 1 < (n : ℕ)) :
    Fintype.card (M.openBoundaryPlaces j) =
      Nat.log (n : ℕ) (Nat.card (finiteResidue M n j hj hn xi).range) + 1 := by
  rw [natCard_finiteResidue_range M ε n j hj hn xi v₀, Nat.log_pow hn₁]
  have : Nonempty (M.openBoundaryPlaces j) := ⟨v₀⟩
  have hpos := Fintype.card_pos (α := M.openBoundaryPlaces j)
  omega

end AnabelianGeometry.WeightFiltration

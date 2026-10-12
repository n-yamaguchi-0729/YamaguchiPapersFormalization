/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenDivisorCohomologyComparison
import Nyll.JacobianVarieties.Kummer.OpenDivisorCardinality

/-! # Cardinality of actual finite-coefficient H¹ of an open curve -/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra TopologicalSpace

namespace AlgebraicCurve.CurveModel

/-- The actual derived finite-coefficient H¹ of a smooth open curve with
nonempty boundary has cardinality n^(2g+r-1). The comparison is supplied
by the actual Kummer covers, not by an assumed cohomology model. -/
theorem natCard_open_finiteH1_eq_pow_genus_boundary
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Fintype (M.openBoundaryPlaces j)] (v₀ : M.openBoundaryPlaces j)
    (n : ℕ+) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) :
    Nat.card (Sheaf.H.{0}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
      (n : ℕ) ^ (2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1) := by
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  calc
    Nat.card (Sheaf.H.{0}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
        Nat.card (Additive (Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n ⧸
          Pic0.openKummerPowers K F (M.openBoundaryPlaces j) n)) :=
      Nat.card_congr (OpenKummer.quotientCohomologyEquiv M n j hj hn xi).symm.toEquiv
    _ = Nat.card (Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n ⧸
          Pic0.openKummerPowers K F (M.openBoundaryPlaces j) n) := rfl
    _ = (n : ℕ) ^ (2 * genusFF K F + Fintype.card (M.openBoundaryPlaces j) - 1) :=
      M.natCard_openKummerQuotient ε (M.openBoundaryPlaces j) v₀ n

end AlgebraicCurve.CurveModel

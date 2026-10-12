/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidues
import Nyll.JacobianVarieties.Kummer.OpenDivisorCardinality

/-!
# Genus and boundary ranks in the actual residue sequence

The kernel has n^(2g) elements and the residue image has n^(r-1) elements.
These counts apply to the actual cohomology maps constructed from Kummer
covers. Intrinsic recognition of this filtration from arithmetic Galois
action is not assumed here.
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

/-- The actual residue kernel is the proper divisorial Kummer quotient. -/
def properKummerEquivFiniteResidueKernel :
    Additive (Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n) ≃
      (finiteResidue M n j hj hn xi).ker :=
  (Equiv.ofInjective (properKummerToFiniteH1 M n j hj hn xi)
    (properKummerToFiniteH1_injective M n j hj hn xi)).trans
      (Equiv.cast (congrArg (fun H : AddSubgroup (FiniteKummerH1 K X n) => ↥H)
        (properKummerToFiniteH1_range M n j hj hn xi)))

include ε

/-- Genus appears as half the exponent in the cardinality of the actual
finite-coefficient residue kernel. -/
theorem natCard_finiteResidue_ker :
    Nat.card (finiteResidue M n j hj hn xi).ker =
      (n : ℕ) ^ (2 * genusFF K F) := by
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := (baseToFunctionField M.toBase).toAlgebra
    let e : F ≃ₐ[K] M.C.functionField :=
      AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (AlgebraicCurve.essFiniteType_functionField M.toBase)
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  calc
    Nat.card (finiteResidue M n j hj hn xi).ker =
        Nat.card (Additive (Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n)) :=
      (Nat.card_congr (properKummerEquivFiniteResidueKernel M n j hj hn xi)).symm
    _ = Nat.card (Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n) := rfl
    _ = Nat.card (Pic0.torsion K F (n : ℕ)) :=
      Nat.card_congr (Pic0.kummerDivisorEquiv K F n).toEquiv
    _ = Nat.card (FiniteKummerH1 K M.C n) :=
      Nat.card_congr (M.kummerTorsionCohomologyEquiv n hn ε.val).toEquiv
    _ = (n : ℕ) ^ (2 * genusFF K F) :=
      M.natCard_finiteH1_eq_pow_genus ε n ε.val

variable [Fintype (M.openBoundaryPlaces j)]

omit [CharZero K] in
/-- A nonempty boundary of size r contributes n^(r-1) actual residue classes. -/
theorem natCard_finiteResidue_range (v₀ : M.openBoundaryPlaces j) :
    Nat.card (finiteResidue M n j hj hn xi).range =
      (n : ℕ) ^ (Fintype.card (M.openBoundaryPlaces j) - 1) := by
  rw [finiteResidue_range M n j hj hn xi ε v₀]
  exact JacobianVarieties.Kummer.natCard_boundaryResidueGroup v₀ n

end AnabelianGeometry.WeightFiltration

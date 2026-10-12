/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.JacobianVarieties.Kummer.OpenBoundaryRelation
import Nyll.JacobianVarieties.Kummer.BoundaryResidueCardinality
import Nyll.JacobianVarieties.Kummer.FiniteH1Cardinality
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed

/-!
# Cardinality of open divisorial Kummer classes

The actual quotient of functions unramified away from the boundary by
actual powers has n^(2g+r-1) elements for a nonempty finite boundary.
The proof uses its exact residue sequence, actual Pic⁰ torsion, and the
proved geometric Picard cardinality calculation. Identification with
derived H¹ of the open curve is not assumed or asserted here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open scoped BigOperators
open JacobianVarieties.Kummer

namespace AlgebraicCurve.CurveModel

/-- The image of the actual quotient residue map consists exactly of
the actual sum-zero boundary residue vectors. -/
def openKummerResidueRangeEquiv
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (S : Set (Place K F)) [Fintype S] (v₀ : S)
    (n : ℕ+) (hchar : ((n : ℕ) : K) ≠ 0) :
    (Pic0.openKummerResidueQuotient S n).range ≃ boundaryResidueGroup S n where
  toFun x := ⟨Multiplicative.toAdd x.val, by
    obtain ⟨q, hq⟩ := x.property
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    change (∑ v : S, Multiplicative.toAdd x.val v) = 0
    rw [← hq]
    exact M.sum_openKummerResidue_eq_zero_set S n u⟩
  invFun a := ⟨Multiplicative.ofAdd a.val, by
    obtain ⟨u, hu⟩ := M.exists_openKummerUnits_of_sum_eq_zero
      ε S v₀ n hchar a.val a.property
    exact ⟨QuotientGroup.mk u, hu⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The kernel of the quotient residue map is the proper divisorial
Kummer quotient, without adding identifications or abstract comparison data. -/
def properKummerQuotientEquivResidueKernel
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Set (Place K F)) (n : ℕ+) :
    Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n ≃
      (Pic0.openKummerResidueQuotient S n).ker :=
  (Equiv.ofInjective (Pic0.kummerQuotientToOpen S n)
    (Pic0.kummerQuotientToOpen_injective S n)).trans
      (Equiv.cast (congrArg
        (fun H : Subgroup (Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) =>
          ↥H) (Pic0.kummerQuotientToOpen_range S n)))

/-- The cardinality formula for actual divisorial Kummer classes on the
complement of a nonempty finite set of places, in characteristic zero. -/
theorem natCard_openKummerQuotient
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (S : Set (Place K F)) [Fintype S] (v₀ : S) (n : ℕ+) :
    Nat.card (Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) =
      (n : ℕ) ^ (2 * genusFF K F + Fintype.card S - 1) := by
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := (AlgebraicCurve.baseToFunctionField M.toBase).toAlgebra
    let e : F ≃ₐ[K] M.C.functionField :=
      AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (AlgebraicCurve.essFiniteType_functionField M.toBase)
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  have hchar : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let f := Pic0.openKummerResidueQuotient S n
  have hker : Nat.card f.ker = (n : ℕ) ^ (2 * genusFF K F) := by
    calc
      Nat.card f.ker = Nat.card (Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n) :=
        (Nat.card_congr (properKummerQuotientEquivResidueKernel S n)).symm
      _ = Nat.card (Pic0.torsion K F (n : ℕ)) :=
        Nat.card_congr (Pic0.kummerDivisorEquiv K F n).toEquiv
      _ = Nat.card (Sheaf.H.{0}
          ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj
            (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) :=
        Nat.card_congr (M.kummerTorsionCohomologyEquiv n
          (isUnit_iff_ne_zero.mpr hchar) ε.val).toEquiv
      _ = (n : ℕ) ^ (2 * genusFF K F) :=
        M.natCard_finiteH1_eq_pow_genus ε n ε.val
  have hrange : Nat.card f.range = (n : ℕ) ^ (Fintype.card S - 1) := by
    calc
      Nat.card f.range = Nat.card (boundaryResidueGroup S n) :=
        Nat.card_congr (M.openKummerResidueRangeEquiv ε S v₀ n hchar)
      _ = (n : ℕ) ^ (Fintype.card S - 1) :=
        natCard_boundaryResidueGroup v₀ n
  have hquot :
      Nat.card ((Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) ⧸ f.ker) =
        Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hS : 1 ≤ Fintype.card S := Fintype.card_pos_iff.mpr ⟨v₀⟩
  calc
    Nat.card (Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) =
        Nat.card ((Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) ⧸ f.ker) *
          Nat.card f.ker := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    _ = (n : ℕ) ^ (Fintype.card S - 1) * (n : ℕ) ^ (2 * genusFF K F) := by
      rw [hquot, hrange, hker]
    _ = (n : ℕ) ^ (2 * genusFF K F + Fintype.card S - 1) := by
      rw [← pow_add]
      congr 1
      omega

end AlgebraicCurve.CurveModel

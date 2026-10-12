/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverCharacterProduct
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverSplitting
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Actual open divisorial Kummer classes inject into derived H¹

The constructed cover supplies the map; multiplication is checked on actual
generic roots, and its kernel is exactly the actual subgroup of powers.
Surjectivity requires the converse interior valuation calculation.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Cohomology TopologicalSpace

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- The actual character kernel is exactly the subgroup of actual powers. -/
theorem kummerMonodromyHom_ker :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    (kummerMonodromyHom M S n j hj hinterior hn xi).ker =
      Pic0.openKummerPowers K F S n := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  apply Subgroup.ext
  intro w
  change kummerMonodromyCharacter M S n w j hj hinterior hn xi = 1 ↔
    w ∈ Pic0.openKummerPowers K F S n
  exact (kummerMonodromyCharacter_eq_one_iff_exists_section
    M S n w j hj hinterior hn xi).trans
      (mem_openKummerPowers_iff_exists_section M S n w j hj hinterior hn).symm

/-- Actual functions modulo actual powers determine actual characters. -/
def quotientCharacter :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    (Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) →*
      (Aut (FiniteEtale.fiber xi) →ₜ* rootsOfUnity (n : ℕ) K) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  exact QuotientGroup.lift (Pic0.openKummerPowers K F S n)
    (kummerMonodromyHom M S n j hj hinterior hn xi)
    (kummerMonodromyHom_ker M S n j hj hinterior hn xi).ge

/-- Distinct open divisorial Kummer classes have distinct actual characters. -/
theorem quotientCharacter_injective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Function.Injective (quotientCharacter M S n j hj hinterior hn xi) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  exact (QuotientGroup.injective_lift_iff (Pic0.openKummerPowers K F S n)
    (kummerMonodromyHom M S n j hj hinterior hn xi)
    (kummerMonodromyHom_ker M S n j hj hinterior hn xi).ge).mpr
      (kummerMonodromyHom_ker M S n j hj hinterior hn xi).symm

/-- The quotient character is the character of its original normalized cover. -/
theorem quotientCharacter_mk (w : Pic0.openKummerUnits K F S n) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    quotientCharacter M S n j hj hinterior hn xi (QuotientGroup.mk w) =
      kummerMonodromyCharacter M S n w j hj hinterior hn xi := rfl

/-- The actual quotient maps additively to genuine derived étale H¹. -/
def quotientCohomology :
    Additive (Pic0.openKummerUnits K F S n ⧸ Pic0.openKummerPowers K F S n) →+
      Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let κ := (quotientCharacter M S n j hj hinterior hn xi).toAdditive
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv A xi).symm.toAddMonoidHom.comp κ

/-- No nonzero actual open divisorial Kummer class maps to zero in derived H¹. -/
theorem quotientCohomology_injective :
    Function.Injective (quotientCohomology M S n j hj hinterior hn xi) := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv A xi).symm.injective.comp
    (quotientCharacter_injective M S n j hj hinterior hn xi)

/-- The additive map retains the genuine class of the original cover. -/
theorem quotientCohomology_mk (w : Pic0.openKummerUnits K F S n) :
    quotientCohomology M S n j hj hinterior hn xi
      (Additive.ofMul (QuotientGroup.mk w)) =
        kummerEtaleClass M S n w j hj hinterior hn xi := rfl

end AlgebraicCurve.CurveModel.OpenKummer

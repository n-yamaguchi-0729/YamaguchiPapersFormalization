/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverCharacterProduct
import Nyll.JacobianVarieties.Kummer.CurveCoverCharacter
import Nyll.JacobianVarieties.Kummer.CurveCoverSplitting
import Nyll.JacobianVarieties.Kummer.DivisorClasses
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Torsion divisor classes inject into actual etale H¹

The actual Kummer character is multiplicative and has exactly the subgroup
of powers as its kernel. It therefore descends injectively through the proved
divisorial Kummer quotient. The proved finite H¹ comparison then supplies an
injective additive map to actual derived etale cohomology. Surjectivity is not
asserted here.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)

/-- The actual Kummer-character kernel consists precisely of actual powers
of functions, as detected by splitting of the original cover. -/
theorem kummerMonodromyHom_ker :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    (M.kummerMonodromyHom n hn xi).ker = Pic0.kummerPowers K F n := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  rw [← Pic0.kummerClass_ker]
  apply Subgroup.ext
  intro u
  change M.kummerMonodromyCharacter n u hn xi = 1 ↔ Pic0.kummerClass n u = 1
  exact (M.kummerMonodromyCharacter_eq_one_iff_exists_section n u hn xi).trans
    (M.kummerClass_eq_one_iff_exists_section n hn u).symm

/-- The actual torsion divisor class determines a continuous character of
the actual fundamental group, via its proved Kummer representative quotient. -/
def kummerTorsionCharacter :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Multiplicative (Pic0.torsion K F n) →*
      (Aut (FiniteEtale.fiber xi) →ₜ* rootsOfUnity (n : ℕ) K) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  exact (QuotientGroup.lift (Pic0.kummerPowers K F n) (M.kummerMonodromyHom n hn xi)
    (M.kummerMonodromyHom_ker n hn xi).ge).comp
      (Pic0.kummerDivisorEquiv K F n).symm.toMonoidHom

/-- No nonzero actual torsion divisor class has trivial Kummer monodromy. -/
theorem kummerTorsionCharacter_injective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Function.Injective (M.kummerTorsionCharacter n hn xi) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  exact ((QuotientGroup.injective_lift_iff (Pic0.kummerPowers K F n)
    (M.kummerMonodromyHom n hn xi) (M.kummerMonodromyHom_ker n hn xi).ge).mpr
      (M.kummerMonodromyHom_ker n hn xi).symm).comp
        (Pic0.kummerDivisorEquiv K F n).symm.injective

/-- Evaluation on an actual represented divisor class is the character of
the original normalized Kummer cover for that function. -/
theorem kummerTorsionCharacter_kummerClass (u : Pic0.kummerUnits K F n) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    M.kummerTorsionCharacter n hn xi (Pic0.kummerClass n u) =
      M.kummerMonodromyCharacter n u hn xi := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  rw [← Pic0.kummerDivisorEquiv_mk]
  change QuotientGroup.lift (Pic0.kummerPowers K F n) (M.kummerMonodromyHom n hn xi)
    (M.kummerMonodromyHom_ker n hn xi).ge
      ((Pic0.kummerDivisorEquiv K F n).symm
        ((Pic0.kummerDivisorEquiv K F n) (QuotientGroup.mk u))) = _
  rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk']
  rfl

include xi

/-- Actual torsion divisor classes map to the actual derived etale H¹ with
constant roots-of-unity coefficients. -/
def kummerTorsionCohomology :
    Pic0.torsion K F n →+
      Sheaf.H.{u} ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let κ : Pic0.torsion K F n →+
      Additive (Aut (FiniteEtale.fiber xi) →ₜ* rootsOfUnity (n : ℕ) K) :=
    (M.kummerTorsionCharacter n hn xi).toAdditive
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv A xi).symm.toAddMonoidHom.comp κ

/-- The map from actual torsion divisor classes to genuine etale H¹ is injective. -/
theorem kummerTorsionCohomology_injective :
    Function.Injective (M.kummerTorsionCohomology n hn xi) := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv A xi).symm.injective.comp
    (M.kummerTorsionCharacter_injective n hn xi)

/-- The descended H¹ map retains the actual Kummer covering class on every
represented divisor class. -/
theorem kummerTorsionCohomology_kummerClass (u : Pic0.kummerUnits K F n) :
    M.kummerTorsionCohomology n hn xi (Multiplicative.toAdd (Pic0.kummerClass n u)) =
      M.kummerEtaleClass n u hn xi := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  have he := M.kummerTorsionCharacter_kummerClass n hn xi u
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  change (finiteH1CharacterEquiv A xi).symm
    (Additive.ofMul (M.kummerTorsionCharacter n hn xi (Pic0.kummerClass n u))) =
      (finiteH1CharacterEquiv A xi).symm
        (Additive.ofMul (M.kummerMonodromyCharacter n u hn xi))
  exact congrArg (fun χ => (finiteH1CharacterEquiv A xi).symm (Additive.ofMul χ)) he

end AlgebraicCurve.CurveModel

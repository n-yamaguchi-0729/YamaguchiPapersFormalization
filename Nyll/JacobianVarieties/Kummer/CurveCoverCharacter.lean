/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverTorsor
import Nyll.JacobianVarieties.Kummer.CurveCoverAction
import Nyll.JacobianVarieties.Kummer.CurveCoverSplitting
import Nyll.EtaleFundamentalGroups.GeometricFiber.FixedPointSections
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison

/-!
# The actual monodromy character and cohomology class of a Kummer cover

The character comes from the proved root-scaling torsor structure on the
original finite etale cover. The actual derived H¹ comparison then constructs
a degree-one etale cohomology class. Its vanishing is equivalent to splitting
of that cover, and hence to vanishing of the actual divided divisor class.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C)

/-- The displacement character of monodromy on the actual normalized
Kummer cover, with the discrete topology on its roots of unity. -/
def kummerMonodromyCharacter :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    Aut (FiniteEtale.fiber ξ) →ₜ* rootsOfUnity (n : ℕ) K := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := M.kummerGeometricRootTorsor n u hn ξ
  have := M.kummerGeometricRootAction_commutes n u hn ξ
  exact torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T.nonempty)

/-- Every point of the original fiber computes the same displacement character. -/
theorem kummerMonodromyCharacter_eq_torsorCharacter
    (x : (FiniteEtale.fiber ξ).obj (M.kummerCover n hn u)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let := M.kummerGeometricRootTorsor n u hn ξ
    let := M.kummerGeometricRootAction_commutes n u hn ξ
    M.kummerMonodromyCharacter n u hn ξ = torsorCharacter x := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := M.kummerGeometricRootTorsor n u hn ξ
  have := M.kummerGeometricRootAction_commutes n u hn ξ
  exact torsorCharacter_eq (Classical.choice T.nonempty) x

/-- Triviality of the actual Kummer monodromy character is equivalent to a
section of the original cover, including when that cover is disconnected. -/
theorem kummerMonodromyCharacter_eq_one_iff_exists_section :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    M.kummerMonodromyCharacter n u hn ξ = 1 ↔
      ∃ s : M.C ⟶ (M.kummerCover n hn u).left,
        s ≫ (M.kummerCover n hn u).hom = 𝟙 M.C := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := M.kummerGeometricRootTorsor n u hn ξ
  have := M.kummerGeometricRootAction_commutes n u hn ξ
  rw [FiniteEtale.exists_section_iff_exists_fiber_fixed ξ (M.kummerCover n hn u)]
  constructor
  · intro h
    let x := Classical.choice T.nonempty
    refine ⟨x, ?_⟩
    apply (torsorCharacter_eq_one_iff x).mp
    exact (M.kummerMonodromyCharacter_eq_torsorCharacter n u hn ξ x).symm.trans h
  · rintro ⟨x, hx⟩
    exact (M.kummerMonodromyCharacter_eq_torsorCharacter n u hn ξ x).trans
      ((torsorCharacter_eq_one_iff x).mpr hx)

/-- The genuine derived degree-one etale cohomology class of the actual
Kummer covering torsor, using the proved finite-coefficient H¹ comparison. -/
def kummerEtaleClass :
    Sheaf.H.{u} ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv A ξ).symm
    (Additive.ofMul (M.kummerMonodromyCharacter n u hn ξ))

/-- Vanishing of the actual cohomology class detects the actual Kummer
character; the cohomology group here is Sheaf.H, not a divisor-group alias. -/
theorem kummerEtaleClass_eq_zero_iff_character_eq_one :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    M.kummerEtaleClass n u hn ξ = 0 ↔ M.kummerMonodromyCharacter n u hn ξ = 1 := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  change (finiteH1CharacterEquiv A ξ).symm
    (Additive.ofMul (M.kummerMonodromyCharacter n u hn ξ)) = 0 ↔ _
  exact (finiteH1CharacterEquiv A ξ).symm.map_eq_zero_iff

/-- Over algebraically closed constants, vanishing of the genuine Kummer
H¹ class agrees with vanishing of the actual divided principal-divisor class. -/
theorem kummerEtaleClass_eq_zero_iff_kummerClass_eq_one [IsAlgClosed K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    M.kummerEtaleClass n u hn ξ = 0 ↔ Pic0.kummerClass n u = 1 := by
  exact (M.kummerEtaleClass_eq_zero_iff_character_eq_one n u hn ξ).trans
    ((M.kummerMonodromyCharacter_eq_one_iff_exists_section n u hn ξ).trans
      (M.kummerClass_eq_one_iff_exists_section n hn u).symm)

end AlgebraicCurve.CurveModel

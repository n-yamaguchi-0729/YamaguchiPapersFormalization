/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverTorsor
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverAction
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

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups.Cohomology TopologicalSpace
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel.OpenKummer

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
  (w : Pic0.openKummerUnits K F S n)
  {X : Scheme.{u}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hinterior : ∀ (y : X) (x : closedPoints M.C),
    x.val = j y → M.placeOfPoint x ∉ S)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The displacement character of monodromy on the actual normalized
Kummer cover, with the discrete topology on its roots of unity. -/
def kummerMonodromyCharacter :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    Aut (FiniteEtale.fiber ξ) →ₜ* rootsOfUnity (n : ℕ) K := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := kummerGeometricRootTorsor M S n w j hj hinterior hn ξ
  have := kummerGeometricRootAction_commutes M S n w j hj hinterior hn ξ
  exact torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) (Classical.choice T.nonempty)

/-- Every point of the original fiber computes the same displacement character. -/
theorem kummerMonodromyCharacter_eq_torsorCharacter
    (x : (FiniteEtale.fiber ξ).obj (M.openKummerCover S n hn w j hj hinterior)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let := kummerGeometricRootTorsor M S n w j hj hinterior hn ξ
    let := kummerGeometricRootAction_commutes M S n w j hj hinterior hn ξ
    kummerMonodromyCharacter M S n w j hj hinterior hn ξ = torsorCharacter x := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := kummerGeometricRootTorsor M S n w j hj hinterior hn ξ
  have := kummerGeometricRootAction_commutes M S n w j hj hinterior hn ξ
  exact torsorCharacter_eq (Classical.choice T.nonempty) x

/-- Triviality of the actual Kummer monodromy character is equivalent to a
section of the original cover, including when that cover is disconnected. -/
theorem kummerMonodromyCharacter_eq_one_iff_exists_section :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    kummerMonodromyCharacter M S n w j hj hinterior hn ξ = 1 ↔
      ∃ s : X ⟶ (M.openKummerCover S n hn w j hj hinterior).left,
        s ≫ (M.openKummerCover S n hn w j hj hinterior).hom = 𝟙 X := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let T := kummerGeometricRootTorsor M S n w j hj hinterior hn ξ
  have := kummerGeometricRootAction_commutes M S n w j hj hinterior hn ξ
  rw [FiniteEtale.exists_section_iff_exists_fiber_fixed ξ (M.openKummerCover S n hn w j hj
    hinterior)]
  constructor
  · intro h
    let x := Classical.choice T.nonempty
    refine ⟨x, ?_⟩
    apply (torsorCharacter_eq_one_iff x).mp
    exact (kummerMonodromyCharacter_eq_torsorCharacter M S n w j hj hinterior hn ξ x).symm.trans h
  · rintro ⟨x, hx⟩
    exact (kummerMonodromyCharacter_eq_torsorCharacter M S n w j hj hinterior hn ξ x).trans
      ((torsorCharacter_eq_one_iff x).mpr hx)

/-- The genuine derived degree-one etale cohomology class of the actual
Kummer covering torsor, using the proved finite-coefficient H¹ comparison. -/
def kummerEtaleClass :
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact (finiteH1CharacterEquiv A ξ).symm
    (Additive.ofMul (kummerMonodromyCharacter M S n w j hj hinterior hn ξ))

/-- Vanishing of the actual cohomology class detects the actual Kummer
character; the cohomology group here is Sheaf.H, not a divisor-group alias. -/
theorem kummerEtaleClass_eq_zero_iff_character_eq_one :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    kummerEtaleClass M S n w j hj hinterior hn ξ = 0 ↔ kummerMonodromyCharacter M S n w j hj
      hinterior hn ξ = 1 := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  change (finiteH1CharacterEquiv A ξ).symm
    (Additive.ofMul (kummerMonodromyCharacter M S n w j hj hinterior hn ξ)) = 0 ↔ _
  exact (finiteH1CharacterEquiv A ξ).symm.map_eq_zero_iff

/-- Vanishing of the genuine derived H¹ class is equivalent to a
section of this actual normalized open-curve cover. -/
theorem kummerEtaleClass_eq_zero_iff_exists_section :
    kummerEtaleClass M S n w j hj hinterior hn ξ = 0 ↔
      ∃ s : X ⟶ (M.openKummerCover S n hn w j hj hinterior).left,
        s ≫ (M.openKummerCover S n hn w j hj hinterior).hom = 𝟙 X :=
  (kummerEtaleClass_eq_zero_iff_character_eq_one M S n w j hj hinterior hn ξ).trans
    (kummerMonodromyCharacter_eq_one_iff_exists_section M S n w j hj hinterior hn ξ)

end AlgebraicCurve.CurveModel.OpenKummer

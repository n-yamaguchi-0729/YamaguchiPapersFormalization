/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverCharacter
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverCharacter

/-! # Characters of the actual proper and open Kummer cohomology classes -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsSepClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω]

/-- The comparison character of the proper Kummer class is the original
root-scaling monodromy character. -/
theorem h1Character_properKummer (u : Pic0.kummerUnits K F n)
    (ξ : Spec (.of Ω) ⟶ M.C) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ
        (M.kummerEtaleClass n u hn ξ) = M.kummerMonodromyCharacter n u hn ξ := by
  intro htop
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  change ((finiteH1CharacterEquiv A ξ)
    ((finiteH1CharacterEquiv A ξ).symm
      (Additive.ofMul (M.kummerMonodromyCharacter n u hn ξ)))).toMul = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The comparison character of the open Kummer class is the original
root-scaling monodromy character on the open curve. -/
theorem h1Character_openKummer (S : Set (Place K F))
    (u : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hinterior : ∀ (y : X) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S)
    (ξ : Spec (.of Ω) ⟶ X) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ
        (CurveModel.OpenKummer.kummerEtaleClass M S n u j hj hinterior hn ξ) =
      CurveModel.OpenKummer.kummerMonodromyCharacter M S n u j hj hinterior hn ξ := by
  intro htop
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  change ((finiteH1CharacterEquiv A ξ)
    ((finiteH1CharacterEquiv A ξ).symm (Additive.ofMul
      (CurveModel.OpenKummer.kummerMonodromyCharacter M S n u j hj hinterior hn ξ)))).toMul = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end AnabelianGeometry.WeightFiltration

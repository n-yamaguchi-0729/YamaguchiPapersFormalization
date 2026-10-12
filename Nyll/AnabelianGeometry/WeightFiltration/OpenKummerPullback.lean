/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.GenericCohomologyInjection
import Nyll.AnabelianGeometry.WeightFiltration.GenericCohomologyNaturality
import Nyll.AnabelianGeometry.WeightFiltration.FieldCharacterNaturality
import Nyll.AnabelianGeometry.WeightFiltration.KummerCohomologyCharacters
import Nyll.AnabelianGeometry.WeightFiltration.GenericKummerRestriction

/-!
# Proper Kummer classes pull back to the actual open Kummer classes

The proof restricts the two actual derived H¹ classes to the function field,
computes their characters on the same root, and uses generic injectivity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology JacobianVarieties.Kummer

namespace AnabelianGeometry.WeightFiltration

private theorem constantCohomologyPullback_eq
    {Y Z : Scheme} (f : Y ⟶ Z) (A : AddCommGrpCat.{0}) (n : ℕ)
    (a : Sheaf.H.{0} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{0}).obj A) n) :
    EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f A n a =
      JacobianVarieties.Kummer.constantCohomologyPullback f A n a := rfl

/-- Actual compactification pullback agrees with forgetting the boundary
conditions in the Kummer cover, at compatible geometric generic points. -/
theorem properKummer_pullback_eq_openKummer
    {K F : Type} [Field K] [IsSepClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (u : Pic0.kummerUnits K F n)
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hinterior : ∀ (y : X) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S)
    [Algebra M.C.functionField X.functionField]
    (hfield : algebraMap M.C.functionField X.functionField = j.functionFieldMap hj)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra M.C.functionField Ω]
    [IsScalarTower M.C.functionField X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω] [IsSepClosure X.functionField Ω]
    (β : Ω) (hβ : β ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)))
    (hn : IsUnit ((n : ℕ) : K)) :
    let ξp := (Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    let ξo := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))) ≫
      X.fromSpecStalk (genericPoint X)
    EtaleFundamentalGroups.Cohomology.constantCohomologyPullback j
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1
        (M.kummerEtaleClass n u hn ξp) =
      CurveModel.OpenKummer.kummerEtaleClass M S n
        (Pic0.kummerUnitsToOpen S n u) j hj hinterior hn ξo := by
  intro ξp ξo
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let ηo := (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
  let cp := M.kummerEtaleClass n u hn ξp
  let co := CurveModel.OpenKummer.kummerEtaleClass M S n
    (Pic0.kummerUnitsToOpen S n u) j hj hinterior hn ξo
  apply finiteH1Pullback_genericPoint_injective X Ω A
  change EtaleFundamentalGroups.Cohomology.constantCohomologyPullback
    (X.fromSpecStalk (genericPoint X)) A 1
    (EtaleFundamentalGroups.Cohomology.constantCohomologyPullback j A 1 cp) =
      EtaleFundamentalGroups.Cohomology.constantCohomologyPullback
        (X.fromSpecStalk (genericPoint X)) A 1 co
  rw [finiteH1Pullback_genericPoint j hj ηo A]
  have hspec : Spec.map (CommRingCat.ofHom (j.functionFieldMap hj)) =
      (Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField X.functionField))) := by
    rw [← hfield]
  rw [hspec]
  simp only [constantCohomologyPullback_eq]
  apply h1Character_injective A ηo
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨σ, rfl⟩ :=
    (FiniteEtale.absoluteGaloisToFiberAutMulEquiv X.functionField Ω inferInstance).surjective γ
  rw [h1Character_fieldPullback]
  rw [h1Character_constantCohomologyPullback,
    h1Character_constantCohomologyPullback]
  change h1Character A ξp (M.kummerEtaleClass n u hn ξp) _ =
    h1Character A ξo (CurveModel.OpenKummer.kummerEtaleClass M S n
      (Pic0.kummerUnitsToOpen S n u) j hj hinterior hn ξo) _
  rw [h1Character_properKummer, h1Character_openKummer]
  exact proper_open_genericKummerCharacter M S n u j hj hinterior hfield β hβ hn σ

end AnabelianGeometry.WeightFiltration

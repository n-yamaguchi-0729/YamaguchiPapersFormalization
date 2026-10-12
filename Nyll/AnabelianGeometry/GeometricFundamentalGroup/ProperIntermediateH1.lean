/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCurveH1Deck
import Nyll.EtaleFundamentalGroups.GaloisCovers.ConnectedCurveModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.CurveModelDeckDegree
import Nyll.EtaleFundamentalGroups.GaloisCovers.DeckIsomorphismTransport
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1IsomorphismPullback
import Nyll.AlgebraicCurves.Models.RationalPointExistence
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed

/-! # Actual intermediate covers of a proper hyperbolic curve

Both intermediate schemes are realized by curve models, with their actual
maps and deck transformations transported through proved isomorphism
squares. Riemann--Hurwitz and actual finite H¹ cardinality then obstruct
surjective pullback. No Galoisness of a chosen model is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry

/-- A map between actual connected finite étale covers of a proper
hyperbolic curve, admitting a nonidentity deck transformation, cannot
induce surjective pullback on actual nontrivial roots-of-unity H¹. -/
theorem not_surjective_finiteH1Pullback_intermediate
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (hg : 2 ≤ genusFF K F)
    (A B : FiniteEtale M.C) [IsConnected A] [IsConnected B]
    (f : A ⟶ B) (σ : Aut (FiniteEtale.mk f.left)) (hσ : σ ≠ 1)
    (n : ℕ+) (hn : 1 < (n : ℕ))
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    ¬ Function.Surjective (constantCohomologyPullback f.left
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1) := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have : IsIntegral A.left := isIntegral_left_of_isConnected_finiteEtale A
  have : IsIntegral B.left := isIntegral_left_of_isConnected_finiteEtale B
  let cA : A.left ⟶ Spec (.of K) := A.hom ≫ M.toBase
  let cB : B.left ⟶ Spec (.of K) := B.hom ≫ M.toBase
  let : Algebra K A.left.functionField := (baseToFunctionField cA).toAlgebra
  let : Algebra K B.left.functionField := (baseToFunctionField cB).toAlgebra
  obtain ⟨hA, hFA, N, eN, heN, _⟩ :=
    exists_curveModel_of_connected_finiteEtale M A
  obtain ⟨hB, hFB, P, eP, heP, hgP⟩ :=
    exists_curveModel_of_connected_finiteEtale M B
  have : Smooth P.toBase := SmoothOfRelativeDimension.smooth 1 P.toBase
  have : IsNormalIntegral P.C := IsNormalIntegral.of_stalks P.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk P.toBase x).2)
  have : GeometricallyIntegral P.toBase := geometricallyIntegral_of_isAlgClosed P.toBase
  have : GeometricallyIntegral N.toBase := geometricallyIntegral_of_isAlgClosed N.toBase
  obtain ⟨εP⟩ := P.nonempty_rationalPoint
  obtain ⟨εN⟩ := N.nonempty_rationalPoint
  let d : N.C ⟶ P.C := eN.hom ≫ f.left ≫ eP.inv
  have : IsFiniteEtale eN.hom := ⟨⟩
  have : IsFiniteEtale eP.inv := ⟨⟩
  have : IsFiniteEtale d := by dsimp only [d]; infer_instance
  have hbase : f.left ≫ cB = cA := by
    dsimp only [cA, cB]
    have hw : f.left ≫ B.hom = A.hom := f.w
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ M.toBase) hw)
  have hd : d ≫ P.toBase = N.toBase := by
    calc
      d ≫ P.toBase = eN.hom ≫ f.left ≫ cB := by
        dsimp only [d]
        rw [← heP]
        simp only [Category.assoc, eP.inv_hom_id_assoc, cB]
      _ = eN.hom ≫ cA := congrArg (fun q => eN.hom ≫ q) hbase
      _ = N.toBase := heN
  have hsq : d ≫ eP.hom = eN.hom ≫ f.left := by
    dsimp only [d]
    simp only [Category.assoc, eP.inv_hom_id, Category.comp_id]
  obtain ⟨ρ, hρ⟩ := FiniteEtale.exists_nontrivial_deck_of_iso_square
    eN eP d f.left hsq σ hσ
  have hdeg := P.one_lt_finrankAlong_of_nontrivial_deck N d hd ρ hρ
  have hnot := not_surjective_finiteH1Pullback_of_hyperbolic
    P N εP εN d hd (hgP hg) hdeg n hn (geom ≫ eN.inv)
  intro hsurj
  apply hnot
  exact constantFiniteH1Pullback_surjective_of_iso_square eN eP
    (geom ≫ eN.inv) (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))
    d f.left hsq hsurj

end AnabelianGeometry

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperIntermediateH1
import Nyll.EtaleFundamentalGroups.Cohomology.CyclicDeckH1Reduction
import Nyll.EtaleFundamentalGroups.Cohomology.ProperH1CoprimeCoefficient

/-! # Faithfulness of actual finite H¹ on proper hyperbolic deck groups

A nonidentity element would yield its actual cyclic intermediate cover.
Choosing coefficients after constructing that cover avoids any
coprimality assumption. Transfer would make all H¹ descend, contradicting
the geometric genus and cohomology cardinality calculation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry

/-- The joint action of the actual deck group on actual finite-coefficient
derived H¹ has trivial kernel for a proper hyperbolic curve. -/
theorem deck_eq_one_of_all_finiteH1_trivial
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (hg : 2 ≤ genusFF K F)
    (A : FiniteEtale M.C) [CategoryTheory.PreGaloisCategory.IsGalois A]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) (σ : Aut A)
    (hσ : ∀ (C : AddCommGrpCat.{0}) [Finite C] c,
      constantCohomologyPullback σ.hom.left C 1 c = c) :
    σ = 1 := by
  classical
  have : ConnectedSpace A.left := FiniteEtale.connectedSpace_left_of_isConnected A
  by_contra hne
  obtain ⟨B, hB, f, hG, ⟨ρ, hρ⟩, hinv⟩ :=
    exists_cyclicIntermediate_of_allFiniteH1Trivial A geom σ hne hσ
  have : IsConnected B := FiniteEtale.isConnected_of_connectedSpace_left B
  have : CategoryTheory.PreGaloisCategory.IsGalois (FiniteEtale.mk f.left) := hG
  have : ConnectedSpace (FiniteEtale.mk f.left).left :=
    inferInstanceAs (ConnectedSpace A.left)
  obtain ⟨n, hn, hcop⟩ :=
    exists_rootsOfUnity_coefficient_coprime_index K (FiniteEtale.mk f.left) geom
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  apply not_surjective_finiteH1Pullback_intermediate M hg A B f ρ hρ n hn geom
  intro c
  exact exists_constantH1Pullback_eq_of_deckInvariant
    (FiniteEtale.mk f.left) geom C hcop c (fun τ => hinv C τ c)

end AnabelianGeometry

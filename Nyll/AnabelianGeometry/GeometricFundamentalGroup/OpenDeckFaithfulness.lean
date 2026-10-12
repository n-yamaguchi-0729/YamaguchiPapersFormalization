/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.OpenIntermediateH1
import Nyll.EtaleFundamentalGroups.Cohomology.CyclicDeckH1Reduction
import Nyll.EtaleFundamentalGroups.Cohomology.ProperH1CoprimeCoefficient

/-! # Faithfulness of actual finite H¹ on open hyperbolic deck groups

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
derived H¹ has trivial kernel for a open hyperbolic curve. -/
theorem open_deck_eq_one_of_all_finiteH1_trivial
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hboundary : (M.openBoundaryPlaces j).Nonempty)
    (hhyperbolic : 0 <
      2 * (genusFF K F : ℤ) + (M.openBoundaryPlaces_finite j).toFinset.card - 2)
    (A : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois A]
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
  have : ConnectedSpace B.left := hB
  have : IsConnected B := FiniteEtale.isConnected_of_connectedSpace_left B
  have : CategoryTheory.PreGaloisCategory.IsGalois (FiniteEtale.mk f.left) := hG
  have : ConnectedSpace (FiniteEtale.mk f.left).left :=
    inferInstanceAs (ConnectedSpace A.left)
  obtain ⟨n, hn, hcop⟩ :=
    exists_rootsOfUnity_coefficient_coprime_index K (FiniteEtale.mk f.left) geom
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  apply not_surjective_open_finiteH1Pullback_intermediate M j hboundary hhyperbolic A B f ρ hρ
    n hn geom
  intro c
  exact exists_constantH1Pullback_eq_of_deckInvariant
    (FiniteEtale.mk f.left) geom C hcop c (fun τ => hinv C τ c)

end AnabelianGeometry

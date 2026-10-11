/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.DeckIntermediateScheme
import EtaleFundamentalGroups.Cohomology.FiniteH1DeckKernel

/-! # Actual cyclic intermediate cover for a kernel element of deck H¹ action

This is a reduction by contradiction: a nonidentity kernel element would
produce an actual nontrivial relative Galois cover whose whole deck group
acts trivially. The intermediate scheme and all action comparisons are
constructed, rather than required as hypotheses.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- A nonidentity element in the actual H¹ deck kernel yields an actual
nontrivial cyclic intermediate Galois cover with wholly trivial H¹ action. -/
theorem exists_cyclicIntermediate_of_allFiniteH1Trivial
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S) [IsGalois A]
    [ConnectedSpace A.left]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left)
    (σ : Aut A) (hσne : σ ≠ 1)
    (hσ : ∀ (C : AddCommGrpCat.{0}) [Finite C] c,
      constantCohomologyPullback σ.hom.left C 1 c = c) :
    ∃ (B : FiniteEtale S) (_ : ConnectedSpace B.left) (f : A ⟶ B),
      CategoryTheory.PreGaloisCategory.IsGalois (C := FiniteEtale B.left) (FiniteEtale.mk f.left) ∧
      (∃ ρ : Aut (FiniteEtale.mk f.left), ρ ≠ 1) ∧
      (∀ (C : AddCommGrpCat.{0}) [Finite C] (τ : Aut (FiniteEtale.mk f.left)) c,
        constantCohomologyPullback τ.hom.left C 1 c = c) := by
  obtain ⟨B, hB, f, hG, hdeck, hrel⟩ :=
    FiniteEtale.exists_intermediate_finiteEtale_of_deckSubgroup A geom
      (Subgroup.zpowers (MulOpposite.op σ))
  have hf : σ.hom ≫ f = f :=
    (hdeck σ).mpr (Subgroup.mem_zpowers (MulOpposite.op σ))
  let e : A.left ≅ A.left :=
    (FiniteEtale.forget S ⋙ Over.forget S).mapIso σ
  have hef : e.hom ≫ f.left = f.left :=
    congrArg (fun k : A ⟶ B => k.left) hf
  let ρ : Aut (FiniteEtale.mk f.left) := MorphismProperty.Over.isoMk e hef
  have hρ : ρ ≠ 1 := by
    intro h
    apply hσne
    apply Aut.ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun t : Aut (FiniteEtale.mk f.left) => t.hom.left) h
  refine ⟨B, hB, f, hG, ⟨ρ, hρ⟩, ?_⟩
  intro C hC τ c
  obtain ⟨τ', heq, hτ'⟩ := hrel τ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hτ'
  have hm' := congrArg MulOpposite.unop hm
  simp only [MulOpposite.unop_zpow, MulOpposite.unop_op] at hm'
  have hmem : τ' ∈ Subgroup.zpowers σ := by
    rw [← hm']
    exact Subgroup.zpow_mem (Subgroup.zpowers σ) (Subgroup.mem_zpowers σ) m
  rw [← heq]
  exact constantFiniteH1Pullback_eq_self_of_mem_deck_zpowers A geom C σ τ' (hσ C) hmem c

end EtaleFundamentalGroups.Cohomology

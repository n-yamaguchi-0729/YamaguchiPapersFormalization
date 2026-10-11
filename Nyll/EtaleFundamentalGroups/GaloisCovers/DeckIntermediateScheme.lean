/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.DeckSubgroupIntermediate
import Nyll.EtaleFundamentalGroups.GaloisCovers.RelativeGalois

/-! # Actual intermediate finite étale Galois covers

Every subgroup of the original deck group is realized by an intermediate
scheme. Relative deck transformations are identified on their actual scheme
maps, not through an assumed comparison field.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

/-- A prescribed deck subgroup gives an actual connected intermediate scheme
and an actual relative Galois cover with exactly that relative deck group. -/
theorem exists_intermediate_finiteEtale_of_deckSubgroup
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S) [IsGalois A]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) (H : Subgroup (Aut A)ᵐᵒᵖ) :
    ∃ (B : FiniteEtale S) (_ : ConnectedSpace B.left) (f : A ⟶ B),
      IsGalois (C := FiniteEtale B.left) (FiniteEtale.mk f.left) ∧
      (∀ σ : Aut A, σ.hom ≫ f = f ↔ MulOpposite.op σ ∈ H) ∧
      (∀ τ : Aut (FiniteEtale.mk f.left), ∃ σ : Aut A,
        σ.hom.left = τ.hom.left ∧ MulOpposite.op σ ∈ H) := by
  let geomBase : Spec (.of Ω) ⟶ S := geom ≫ A.hom
  let q : Over.mk geomBase ⟶ A.toComma := Over.homMk geom rfl
  let x : (fiber geomBase).obj A := (fiberObjEquivHom geomBase A).symm q
  obtain ⟨B, hB, y, f, _, hdeck⟩ :=
    exists_intermediateObject_of_deckSubgroup (fiber geomBase) A x H
  have : ConnectedSpace B.left := connectedSpace_left_of_isConnected B
  refine ⟨B, inferInstance, f, isGalois_over_intermediate A B f geom, hdeck, ?_⟩
  intro τ
  let e : A.left ≅ A.left :=
    (FiniteEtale.forget B.left ⋙ Over.forget B.left).mapIso τ
  have herel : e.hom ≫ f.left = f.left := τ.hom.w
  have hebase : e.hom ≫ A.hom = A.hom := by
    rw [← MorphismProperty.Over.w f, ← Category.assoc, herel]
  let σ : Aut A := MorphismProperty.Over.isoMk e hebase
  have hσ : σ.hom ≫ f = f := by
    apply MorphismProperty.Over.Hom.ext
    exact herel
  exact ⟨σ, rfl, (hdeck σ).mp hσ⟩

end AlgebraicGeometry.FiniteEtale

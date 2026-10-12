/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-! # Transport of actual deck transformations through scheme isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

/-- A proved isomorphism square transports a nonidentity actual deck
transformation to a nonidentity actual deck transformation. -/
theorem exists_nontrivial_deck_of_iso_square
    {X Y X' Y' : Scheme}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    [IsFiniteEtale f] [IsFiniteEtale g]
    (hfg : f ≫ eY.hom = eX.hom ≫ g)
    (σ : Aut (FiniteEtale.mk g)) (hσ : σ ≠ 1) :
    ∃ ρ : Aut (FiniteEtale.mk f), ρ ≠ 1 := by
  let a : X' ≅ X' :=
    (FiniteEtale.forget Y' ⋙ Over.forget Y').mapIso σ
  have ha : a.hom ≫ g = g := σ.hom.w
  let b : X ≅ X := eX ≪≫ a ≪≫ eX.symm
  have hb : b.hom ≫ f = f := by
    apply (cancel_mono eY.hom).mp
    change (eX.hom ≫ a.hom ≫ eX.inv) ≫ f ≫ eY.hom = f ≫ eY.hom
    simp only [Category.assoc]
    rw [hfg, eX.inv_hom_id_assoc]
    exact congrArg (fun q : X' ⟶ Y' => eX.hom ≫ q) ha
  let ρ : Aut (FiniteEtale.mk f) := MorphismProperty.Over.isoMk b hb
  refine ⟨ρ, ?_⟩
  intro hρ
  have hbId : eX.hom ≫ a.hom ≫ eX.inv = 𝟙 X :=
    congrArg (fun t : Aut (FiniteEtale.mk f) => t.hom.left) hρ
  have haId := congrArg (fun k : X ⟶ X => eX.inv ≫ k ≫ eX.hom) hbId
  simp only [Category.assoc, eX.inv_hom_id_assoc, eX.inv_hom_id,
    Category.comp_id, Category.id_comp] at haId
  apply hσ
  apply Aut.ext
  apply MorphismProperty.Over.Hom.ext
  exact haId

end AlgebraicGeometry.FiniteEtale

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.PointedCover

/-!
# Geometric deck pullback and the over-category

Pullback along an actual deck automorphism of a finite étale cover is
identified with inverse postcomposition in its over-category. The comparison
is the actual first projection of the scheme pullback.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} (A : FiniteEtale S) (σ : Aut A)

/-- The scheme isomorphism underlying an actual deck transformation. -/
def deckSchemeIso : A.left ≅ A.left where
  hom := σ.hom.left
  inv := σ.inv.left
  hom_inv_id := congrArg (fun f : A ⟶ A => f.left) σ.hom_inv_id
  inv_hom_id := congrArg (fun f : A ⟶ A => f.left) σ.inv_hom_id

private theorem deck_hom_inv :
    σ.hom.left ≫ σ.inv.left = 𝟙 A.left :=
  congrArg (fun f : A ⟶ A => f.left) σ.hom_inv_id

private theorem deck_inv_hom :
    σ.inv.left ≫ σ.hom.left = 𝟙 A.left :=
  congrArg (fun f : A ⟶ A => f.left) σ.inv_hom_id

private def deckPullbackSourceIso (B : FiniteEtale A.left) :
    Limits.pullback B.hom σ.hom.left ≅ B.left where
  hom := Limits.pullback.fst B.hom σ.hom.left
  inv := Limits.pullback.lift (𝟙 B.left) (B.hom ≫ σ.inv.left) (by
    rw [Category.id_comp, Category.assoc, deck_inv_hom A σ]
    exact (Category.comp_id B.hom).symm)
  hom_inv_id := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc,
        Limits.pullback.condition, Category.assoc,
        deck_hom_inv A σ, Category.comp_id, Category.id_comp]
  inv_hom_id := Limits.pullback.lift_fst _ _ _

private def deckPullbackOverObjIso (B : FiniteEtale A.left) :
    (overEquiv A).functor.obj ((pullback σ.hom.left).obj B) ≅
      (Over.map σ.inv).obj ((overEquiv A).functor.obj B) := by
  let e : ((overEquiv A).functor.obj ((pullback σ.hom.left).obj B)).left ≅
      ((overEquiv A).functor.obj B).left :=
    MorphismProperty.Over.isoMk (deckPullbackSourceIso A σ B) (by
      change Limits.pullback.fst B.hom σ.hom.left ≫ (B.hom ≫ A.hom) =
        Limits.pullback.snd B.hom σ.hom.left ≫ A.hom
      rw [← Category.assoc, Limits.pullback.condition, Category.assoc,
        MorphismProperty.Over.w σ.hom])
  exact Over.isoMk e (by
    apply MorphismProperty.Over.Hom.ext
    change Limits.pullback.fst B.hom σ.hom.left ≫ (B.hom ≫ σ.inv.left) =
      Limits.pullback.snd B.hom σ.hom.left
    rw [← Category.assoc, Limits.pullback.condition, Category.assoc,
      deck_hom_inv A σ, Category.comp_id])

/-- Actual scheme pullback by a deck transformation is inverse
postcomposition under the finite-étale over-category equivalence. -/
def deckPullbackOverIso :
    pullback σ.hom.left ⋙ (overEquiv A).functor ≅
      (overEquiv A).functor ⋙ Over.map σ.inv :=
  NatIso.ofComponents (deckPullbackOverObjIso A σ) (fun f => by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    change ((pullback σ.hom.left).map f).left ≫
        Limits.pullback.fst _ σ.hom.left =
      Limits.pullback.fst _ σ.hom.left ≫ f.left
    exact Limits.pullback.lift_fst _ _ _)

/-- The comparison uses the actual first projection, not a chosen
isomorphism between the covering schemes. -/
theorem deckPullbackOverIso_hom_left (B : FiniteEtale A.left) :
    ((deckPullbackOverIso A σ).hom.app B).left.left =
      Limits.pullback.fst B.hom σ.hom.left := rfl

end AlgebraicGeometry.FiniteEtale

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiniteH1PullbackIdentity

/-! # Transporting actual finite H¹ along geometric isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- The existing derived pullback along a scheme isomorphism is an
additive equivalence, with inverse the actual inverse-morphism pullback. -/
def constantFiniteH1PullbackEquiv
    {X Y : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
    (e : X ≅ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A] :
    Sheaf.H.{0} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1 ≃+
      Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1 where
  toFun := constantCohomologyPullback e.hom A 1
  invFun := constantCohomologyPullback e.inv A 1
  left_inv c := by
    rw [← constantFiniteH1Pullback_comp e.inv e.hom (geom ≫ e.hom) A c,
      e.inv_hom_id, constantFiniteH1Pullback_id (geom ≫ e.hom) A c]
  right_inv c := by
    rw [← constantFiniteH1Pullback_comp e.hom e.inv geom A c,
      e.hom_inv_id, constantFiniteH1Pullback_id geom A c]
  map_add' a b := map_add (constantCohomologyPullback e.hom A 1) a b

/-- Triviality of an actual endomorphism's H¹ action is preserved under an
actual geometric isomorphism and a proved commuting square. -/
theorem constantFiniteH1Pullback_eq_self_of_iso_square
    {X Y : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
    (e : X ≅ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (f : X ⟶ X) (g : Y ⟶ Y) (hfg : f ≫ e.hom = e.hom ≫ g)
    (hg : ∀ c, constantCohomologyPullback g A 1 c = c) :
    ∀ c, constantCohomologyPullback f A 1 c = c := by
  intro c
  obtain ⟨b, rfl⟩ := (constantFiniteH1PullbackEquiv e geom A).surjective c
  change constantCohomologyPullback f A 1 (constantCohomologyPullback e.hom A 1 b) =
    constantCohomologyPullback e.hom A 1 b
  rw [← constantFiniteH1Pullback_comp f e.hom geom A b, hfg,
    constantFiniteH1Pullback_comp e.hom g geom A b, hg b]

/-- Surjectivity of actual derived finite H¹ pullback is invariant under
a proved square of scheme isomorphisms. -/
theorem constantFiniteH1Pullback_surjective_of_iso_square
    {X Y X' Y' : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
    [ConnectedSpace X'] [ConnectedSpace Y']
    (eX : X ≅ X') (eY : Y ≅ Y')
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (hfg : f ≫ eY.hom = eX.hom ≫ g)
    (hg : Function.Surjective (constantCohomologyPullback g A 1)) :
    Function.Surjective (constantCohomologyPullback f A 1) := by
  intro c
  obtain ⟨b, hb⟩ := (constantFiniteH1PullbackEquiv eX geom A).surjective c
  obtain ⟨a, ha⟩ := hg b
  refine ⟨constantCohomologyPullback eY.hom A 1 a, ?_⟩
  rw [← constantFiniteH1Pullback_comp f eY.hom geom A a, hfg,
    constantFiniteH1Pullback_comp eX.hom g geom A a, ha]
  exact hb

end EtaleFundamentalGroups.Cohomology

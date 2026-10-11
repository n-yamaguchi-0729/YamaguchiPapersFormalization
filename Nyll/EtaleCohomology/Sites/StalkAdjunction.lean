/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Stalks of a left adjoint to restriction

Let `G` be a continuous functor of sites. A comparison of the fiber functors
of two points induces a comparison of their skyscraper functors. If `L` is
left adjoint to restriction along `G`, taking mates gives the corresponding
comparison of stalks after `L`.

When the restricted fiber functor has no elements, the restricted skyscraper
and the stalk after `L` are zero. The coefficient category needs products and,
for stalks, colimits of the size of the points. Only the vanishing statements
require zero morphisms. No scheme, field, coefficient ring, or abelian-category
hypothesis is used.

The geometric comparisons and the adjunction are supplied by concrete
constructions when this result is applied to extension by zero.
-/


noncomputable section

universe w uC vC uD vD uA vA

open CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology.Sites

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsContinuous J K]
  (A : Type uA) [Category.{vA} A] [HasProducts.{w} A]
  (Φ : K.Point.{w}) (Ψ : J.Point.{w}) (e : G ⋙ Φ.fiber ≅ Ψ.fiber)

/-- A comparison of fiber functors gives a comparison of restricted skyscrapers. -/
def restrictionSkyscraperIso :
    Φ.skyscraperSheafFunctor (A := A) ⋙ G.sheafPushforwardContinuous A J K ≅
      Ψ.skyscraperSheafFunctor :=
  ((fullyFaithfulSheafToPresheaf J A).whiskeringRight A).preimageIso
    ((flipFunctor Cᵒᵖ A A).mapIso
      (CategoryTheory.Functor.isoWhiskerRight (NatIso.op e).symm piFunctor.flip))

variable [HasColimitsOfSize.{w, w} A]
  (L : Sheaf J A ⥤ Sheaf K A) (adj : L ⊣ G.sheafPushforwardContinuous A J K)

/-- A left adjoint to restriction has the stalk specified by the fiber comparison. -/
def adjunctionStalkIso : L ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber :=
  ((conjugateIsoEquiv (adj.comp Φ.skyscraperSheafAdjunction)
    Ψ.skyscraperSheafAdjunction).symm (restrictionSkyscraperIso G A Φ Ψ e)).symm

variable [HasZeroMorphisms A]

omit [HasColimitsOfSize.{w, w} A] in
/-- Restricting a skyscraper gives zero when all its indexing sets are empty. -/
lemma restrictionSkyscraper_isZero
    (h : ∀ V : C, IsEmpty (Φ.fiber.obj (G.obj V))) (M : A) :
    IsZero ((G.sheafPushforwardContinuous A J K).obj (Φ.skyscraperSheafFunctor.obj M)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (sheafToPresheaf J A).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  apply NatTrans.ext
  funext V
  change 𝟙 (∏ᶜ fun (_ : Φ.fiber.obj (G.obj V.unop)) => M) = 0
  apply Pi.hom_ext
  intro a
  exact ((h V.unop).false a).elim

include adj in
/-- The stalk after a left adjoint to restriction vanishes when its fiber has no lifts. -/
lemma adjunctionStalk_isZero
    (h : ∀ V : C, IsEmpty (Φ.fiber.obj (G.obj V))) (F : Sheaf J A) :
    IsZero (Φ.sheafFiber.obj (L.obj F)) := by
  let a := adj.comp Φ.skyscraperSheafAdjunction
  let M := Φ.sheafFiber.obj (L.obj F)
  have hz := restrictionSkyscraper_isZero (J := J) G A Φ h M
  rw [IsZero.iff_id_eq_zero]
  apply (a.homEquiv F M).injective
  exact hz.eq_of_tgt _ _

end EtaleCohomology.Sites

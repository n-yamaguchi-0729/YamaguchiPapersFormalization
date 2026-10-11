/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.RestrictionStalks
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Canonical counits and initial neighborhood functors

The colimit comparison for restriction agrees, under the stalk/skyscraper
adjunctions, with restriction of maps into skyscraper sheaves. Initiality of
the neighborhood functor therefore makes that restriction bijective on Hom
sets. For any left adjoint to restriction, this proves that the canonical
counit induces an isomorphism on the specified stalk.

The coefficient category only needs products and colimits of the size of the
point. No additive, abelian, or scheme hypothesis is used.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleCohomology.Sites

universe w uC vC uD vD uA vA

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [RepresentablyFlat F] [F.IsContinuous J K]
  (hF : CoverPreserving J K F) (Φ : K.Point.{w})
  [InitiallySmall.{w} (F ⋙ Φ.fiber).Elements]
  (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{w, w} A]
  [(Functor.Elements.precomp F Φ.fiber).Initial]

/-- The stalk comparison sends each section to its image in the original stalk. -/
lemma toPresheafFiber_restrictionComapStalkIso_hom
    (G : Sheaf K A) (X : C) (x : Φ.fiber.obj (F.obj X)) :
    (Φ.comap F hF).toPresheafFiber X x
        ((F.sheafPushforwardContinuous A J K).obj G).obj ≫
      (restrictionComapStalkIso F hF Φ A).hom.app G =
        Φ.toPresheafFiber (F.obj X) x G.obj := by
  let : HasColimitsOfShape (F ⋙ Φ.fiber).Elementsᵒᵖ A :=
    hasColimitsOfShape_of_finallySmall _ _
  exact Functor.Final.ι_colimitIso_hom (Functor.Elements.precomp F Φ.fiber).op
    ((Functor.Elements.π Φ.fiber).op ⋙ G.obj) (op ((F ⋙ Φ.fiber).elementsMk X x))

variable [HasProducts.{w} A]

/-- Under the stalk/skyscraper adjunction, the colimit comparison is restriction of maps. -/
lemma restrictionComapStalkIso_homEquiv
    (G : Sheaf K A) (M : A) (a : Φ.sheafFiber.obj G ⟶ M) :
    (Φ.comap F hF).skyscraperSheafAdjunction.homEquiv
        ((F.sheafPushforwardContinuous A J K).obj G) M
        ((restrictionComapStalkIso F hF Φ A).hom.app G ≫ a) =
      (F.sheafPushforwardContinuous A J K).map
        (Φ.skyscraperSheafAdjunction.homEquiv G M a) := by
  apply (sheafToPresheaf J A).map_injective
  change ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv _ M
      ((restrictionComapStalkIso F hF Φ A).hom.app G ≫ a)).hom =
    Functor.whiskerLeft F.op (Φ.skyscraperSheafAdjunction.homEquiv G M a).hom
  refine ((Φ.comap F hF).skyscraperSheafAdjunction_homEquiv_apply_hom _).trans ?_
  refine Eq.trans ?_ (congrArg (Functor.whiskerLeft F.op)
    (Φ.skyscraperSheafAdjunction_homEquiv_apply_hom a).symm)
  apply NatTrans.ext
  funext X
  apply Pi.hom_ext
  intro x
  change ((Φ.comap F hF).skyscraperPresheafHomEquiv
      ((restrictionComapStalkIso F hF Φ A).hom.app G ≫ a)).app (op X.unop) ≫ Pi.π _ x =
    (Φ.skyscraperPresheafHomEquiv a).app (op (F.obj X.unop)) ≫ Pi.π _ x
  refine ((Φ.comap F hF).skyscraperPresheafHomEquiv_app_π _ X.unop x).trans ?_
  refine Eq.trans ?_ (Φ.skyscraperPresheafHomEquiv_app_π a (F.obj X.unop) x).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun b => b ≫ a)
    (toPresheafFiber_restrictionComapStalkIso_hom F hF Φ A G X.unop x))

include hF in
/-- Initiality of the neighborhood functor makes restriction bijective on maps to skyscrapers. -/
lemma restriction_skyscraperHom_bijective (G : Sheaf K A) (M : A) :
    Function.Bijective (fun (a : G ⟶ Φ.skyscraperSheaf M) =>
      (F.sheafPushforwardContinuous A J K).map a) := by
  let e := (Φ.skyscraperSheafAdjunction.homEquiv G M).symm.trans
    ((Iso.homCongr ((restrictionComapStalkIso F hF Φ A).app G).symm (Iso.refl M)).trans
      ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv _ M))
  have he : (fun a => (F.sheafPushforwardContinuous A J K).map a) = e := by
    funext a
    dsimp [e, Iso.homCongr]
    rw [Category.comp_id, restrictionComapStalkIso_homEquiv, Equiv.apply_symm_apply]
  rw [he]
  exact e.bijective

variable (L : Sheaf J A ⥤ Sheaf K A) (adj : L ⊣ F.sheafPushforwardContinuous A J K)

include hF in
/-- The actual adjunction counit is an isomorphism on the stalk with initial neighborhoods. -/
lemma restriction_counit_stalk_isIso (G : Sheaf K A) :
    IsIso (Φ.sheafFiber.map (adj.counit.app G)) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  let e := (adj.comp Φ.skyscraperSheafAdjunction).homEquiv
    ((F.sheafPushforwardContinuous A J K).obj G) M
  rw [← Function.Bijective.of_comp_iff' e.bijective]
  have h := (restriction_skyscraperHom_bijective F hF Φ A G M).comp
    (Φ.skyscraperSheafAdjunction.homEquiv G M).bijective
  change Function.Bijective (fun a : Φ.sheafFiber.obj G ⟶ M =>
    e (Φ.sheafFiber.map (adj.counit.app G) ≫ a))
  have he : (fun a : Φ.sheafFiber.obj G ⟶ M =>
      e (Φ.sheafFiber.map (adj.counit.app G) ≫ a)) =
      ((fun (b : G ⟶ Φ.skyscraperSheaf M) => (F.sheafPushforwardContinuous A J K).map b) ∘
        Φ.skyscraperSheafAdjunction.homEquiv G M) := by
    funext a
    dsimp [e, Function.comp]
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_apply,
      Functor.map_comp, ← Category.assoc, Adjunction.right_triangle_components,
      Category.id_comp]
  rw [he]
  exact h

end EtaleCohomology.Sites

/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The actual unit on an inverse-image stalk

For a continuous functor of sites, restricting a germ at the comapped point
gives a germ at the original point. Composing this concrete comparison with
the adjunction unit is an isomorphism. The proof uses the stalk/skyscraper
adjunctions and computes the map on representing sections; it requires no
initiality of the functor between pointed neighborhoods.
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

/-- A direct-image germ at the comapped point restricts to its original germ. -/
def restrictionComapStalkMap (G : Sheaf K A) :
    (Φ.comap F hF).sheafFiber.obj ((F.sheafPushforwardContinuous A J K).obj G) ⟶
      Φ.sheafFiber.obj G :=
  (Φ.comap F hF).presheafFiberDesc
    (fun U u => Φ.toPresheafFiber (F.obj U) u G.obj)
    (fun _ _ g u => Φ.toPresheafFiber_w (F.map g) u G.obj)

/-- The direct-image stalk comparison sends a representing section to its germ. -/
lemma toPresheafFiber_restrictionComapStalkMap
    (G : Sheaf K A) (U : C) (u : Φ.fiber.obj (F.obj U)) :
    (Φ.comap F hF).toPresheafFiber U u
        ((F.sheafPushforwardContinuous A J K).obj G).obj ≫
      restrictionComapStalkMap F hF Φ A G = Φ.toPresheafFiber (F.obj U) u G.obj :=
  (Φ.comap F hF).toPresheafFiber_presheafFiberDesc _ _ U u

variable [HasProducts.{w} A]

/-- Under the stalk/skyscraper adjunction, the concrete comparison is restriction. -/
lemma restrictionComapStalkMap_homEquiv
    (G : Sheaf K A) (M : A) (a : Φ.sheafFiber.obj G ⟶ M) :
    (Φ.comap F hF).skyscraperSheafAdjunction.homEquiv
        ((F.sheafPushforwardContinuous A J K).obj G) M
        (restrictionComapStalkMap F hF Φ A G ≫ a) =
      (F.sheafPushforwardContinuous A J K).map
        (Φ.skyscraperSheafAdjunction.homEquiv G M a) := by
  apply (sheafToPresheaf J A).map_injective
  change ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv _ M
      (restrictionComapStalkMap F hF Φ A G ≫ a)).hom =
    Functor.whiskerLeft F.op (Φ.skyscraperSheafAdjunction.homEquiv G M a).hom
  refine ((Φ.comap F hF).skyscraperSheafAdjunction_homEquiv_apply_hom _).trans ?_
  refine Eq.trans ?_ (congrArg (Functor.whiskerLeft F.op)
    (Φ.skyscraperSheafAdjunction_homEquiv_apply_hom a).symm)
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro u
  change ((Φ.comap F hF).skyscraperPresheafHomEquiv
      (restrictionComapStalkMap F hF Φ A G ≫ a)).app (op U.unop) ≫ Pi.π _ u =
    (Φ.skyscraperPresheafHomEquiv a).app (op (F.obj U.unop)) ≫ Pi.π _ u
  refine ((Φ.comap F hF).skyscraperPresheafHomEquiv_app_π _ U.unop u).trans ?_
  refine Eq.trans ?_ (Φ.skyscraperPresheafHomEquiv_app_π a (F.obj U.unop) u).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun b => b ≫ a)
    (toPresheafFiber_restrictionComapStalkMap F hF Φ A G U.unop u))

variable (L : Sheaf J A ⥤ Sheaf K A) (adj : L ⊣ F.sheafPushforwardContinuous A J K)

/-- The actual unit followed by restriction of germs is the inverse-image stalk
isomorphism, for any left adjoint to direct image. -/
theorem unit_restrictionComapStalkMap_isIso (G : Sheaf J A) :
    IsIso ((Φ.comap F hF).sheafFiber.map (adj.unit.app G) ≫
      restrictionComapStalkMap F hF Φ A (L.obj G)) := by
  apply isIso_of_coyoneda_map_bijective
  intro M
  let e : (Φ.sheafFiber.obj (L.obj G) ⟶ M) ≃
      ((Φ.comap F hF).sheafFiber.obj G ⟶ M) :=
    ((adj.comp Φ.skyscraperSheafAdjunction).homEquiv G M).trans
      ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv G M).symm
  have he (a : Φ.sheafFiber.obj (L.obj G) ⟶ M) :
      e a = ((Φ.comap F hF).sheafFiber.map (adj.unit.app G) ≫
        restrictionComapStalkMap F hF Φ A (L.obj G)) ≫ a := by
    apply ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv G M).injective
    change ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv G M)
        (((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv G M).symm
          ((adj.comp Φ.skyscraperSheafAdjunction).homEquiv G M a)) = _
    refine (((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv G M).apply_symm_apply
      ((adj.comp Φ.skyscraperSheafAdjunction).homEquiv G M a)).trans ?_
    have hl : (adj.comp Φ.skyscraperSheafAdjunction).homEquiv G M a =
        adj.unit.app G ≫ (F.sheafPushforwardContinuous A J K).map
          (Φ.skyscraperSheafAdjunction.homEquiv (L.obj G) M a) := by
      rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_apply]
    refine hl.trans (Eq.symm ?_)
    refine (congrArg ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv G M)
      (Category.assoc _ _ _)).trans ?_
    refine ((Φ.comap F hF).skyscraperSheafAdjunction.homEquiv_naturality_left
      (adj.unit.app G) (restrictionComapStalkMap F hF Φ A (L.obj G) ≫ a)).trans ?_
    exact congrArg
      (fun b : (F.sheafPushforwardContinuous A J K).obj (L.obj G) ⟶
        (Φ.comap F hF).skyscraperSheaf M => adj.unit.app G ≫ b)
      (restrictionComapStalkMap_homEquiv F hF Φ A (L.obj G) M a)
  have hfun : (fun a : Φ.sheafFiber.obj (L.obj G) ⟶ M =>
      ((Φ.comap F hF).sheafFiber.map (adj.unit.app G) ≫
        restrictionComapStalkMap F hF Φ A (L.obj G)) ≫ a) = e :=
    funext (fun a => (he a).symm)
  rw [hfun]
  exact e.bijective

end EtaleCohomology.Sites

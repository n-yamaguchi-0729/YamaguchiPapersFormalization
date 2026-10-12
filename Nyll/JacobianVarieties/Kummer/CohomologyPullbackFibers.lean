/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Kummer.CohomologyPullback
import Nyll.EtaleCohomology.Classical.AbelianPullbackConstants
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation

/-!
# Actual extension fibers under scheme pullback

The inverse-image adjunction unit sends a lift of the integer section one to
a lift in the actual inverse-image extension. Compatibility with the quotient
comes from the unit's naturality and the proved constant-section comparison.
This constructs the map of actual sheaves used to compare their geometric
monodromy under a morphism of schemes.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u})
  {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) (h : i ≫ p = 0)

private theorem pullbackExtension_unit_projection :
    (etaleAbelianPullbackPushforwardAdjunction f).unit.app E ≫
        (etaleAbelianPushforward f).map (pullbackExtension f A i p h).g =
      p ≫ (etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
        ((etaleAbelianPullbackConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  (etaleAbelianPullbackPushforwardAdjunction f).homEquiv_naturality_left p
    ((etaleAbelianPullbackConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u} ℤ)))

private theorem pullbackExtension_unit_inclusion :
    i ≫ (etaleAbelianPullbackPushforwardAdjunction f).unit.app E =
      (etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
          ((etaleAbelianPullbackConstantIso f).hom.app A) ≫
        (etaleAbelianPushforward f).map (pullbackExtension f A i p h).f := by
  let P := etaleAbelianPullback f
  let R := etaleAbelianPushforward f
  let adj := etaleAbelianPullbackPushforwardAdjunction f
  let e := etaleAbelianPullbackConstantIso f
  calc
    i ≫ adj.unit.app E = adj.unit.app _ ≫ R.map (P.map i) := adj.unit.naturality i
    _ = adj.unit.app _ ≫ R.map (e.hom.app A ≫ (e.inv.app A ≫ P.map i)) := by
      rw [e.hom_inv_id_app_assoc]
    _ = adj.homEquiv _ _ (e.hom.app A) ≫ R.map (e.inv.app A ≫ P.map i) := by
      rw [R.map_comp, ← Category.assoc]
      rfl

private def fiberMap
    {E' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i' : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E')
    (p' : E' ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (h' : i' ≫ p' = 0)
    (η : E ⟶ (etaleAbelianPushforward f).obj E')
    (q : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (etaleAbelianPushforward f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hp : η ≫ (etaleAbelianPushforward f).map p' = p ≫ q)
    (hq : ∀ U : Y.Etaleᵒᵖ,
      q.hom.app U ((integerUnitSection Y).app U PUnit.unit) =
        (integerUnitSection X).app (op ((etaleBaseChange f).obj U.unop)) PUnit.unit) :
    extensionFiber (ShortComplex.mk i p h) (integerUnitSection Y) ⟶
      (etaleSetPushforward f).obj
        (extensionFiber (ShortComplex.mk i' p' h') (integerUnitSection X)) where
  hom :=
    { app := fun U => ↾fun x => ⟨η.hom.app U x.val, by
        have he := ConcreteCategory.congr_hom
          (congrArg (fun m : E ⟶ (etaleAbelianPushforward f).obj
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
              (AddCommGrpCat.of (ULift.{u} ℤ))) => m.hom.app U) hp) x.val
        exact he.trans ((congrArg (q.hom.app U) x.property).trans (hq U))⟩
      naturality := fun U V k => by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (η.hom.naturality k) x.val }

private theorem fiberMap_translation
    {E' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i' : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E')
    (p' : E' ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (h' : i' ≫ p' = 0)
    (η : E ⟶ (etaleAbelianPushforward f).obj E')
    (q : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (etaleAbelianPushforward f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hp : η ≫ (etaleAbelianPushforward f).map p' = p ≫ q)
    (hq : ∀ U : Y.Etaleᵒᵖ,
      q.hom.app U ((integerUnitSection Y).app U PUnit.unit) =
        (integerUnitSection X).app (op ((etaleBaseChange f).obj U.unop)) PUnit.unit)
    (qA : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶
      (etaleAbelianPushforward f).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A))
    (hi : i ≫ η = qA ≫ (etaleAbelianPushforward f).map i')
    (hc : ∀ (U : Y.Etaleᵒᵖ) (a : A), qA.hom.app U
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app U a) =
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
          (op ((etaleBaseChange f).obj U.unop)) a) (a : A) :
    constantFiberTranslation A i p h (integerUnitSection Y) a ≫
        fiberMap f A i p h i' p' h' η q hp hq =
      fiberMap f A i p h i' p' h' η q hp hq ≫
        (etaleSetPushforward f).map
          (constantFiberTranslation A i' p' h' (integerUnitSection X) a) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  change {b : E.obj.obj U // p.hom.app U b = (integerUnitSection Y).app U PUnit.unit} at x
  apply Subtype.ext
  let ηU : E.obj.obj U ⟶ E'.obj.obj (op ((etaleBaseChange f).obj U.unop)) := η.hom.app U
  change ηU (i.hom.app U
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app U a) + x.val) =
    i'.hom.app (op ((etaleBaseChange f).obj U.unop))
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
          (op ((etaleBaseChange f).obj U.unop)) a) + ηU x.val
  rw [map_add]
  apply congrArg (· + ηU x.val)
  have he := ConcreteCategory.congr_hom
    (congrArg (fun m : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶
      (etaleAbelianPushforward f).obj E' => m.hom.app U) hi)
      ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app U a)
  exact he.trans (congrArg (i'.hom.app (op ((etaleBaseChange f).obj U.unop))) (hc U a))

private theorem constantUnit_section (B : AddCommGrpCat.{u}) (U : Y.Etaleᵒᵖ) (b : B) :
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
      ((etaleAbelianPullbackConstantIso f).hom.app B)).hom.app U
        ((toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj B)).app U b) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj B)).app
        (op ((etaleBaseChange f).obj U.unop)) b :=
  ConcreteCategory.congr_hom (etaleAbelianPullbackConstantIso_hom_section f B U.unop) b

/-- The actual adjunction unit maps the original lift sheaf into the direct
image of the lift sheaf of the actual inverse-image extension. -/
def pullbackExtensionFiberMap :
    extensionFiber (ShortComplex.mk i p h) (integerUnitSection Y) ⟶
      (etaleSetPushforward f).obj
        (extensionFiber (pullbackExtension f A i p h) (integerUnitSection X)) :=
  fiberMap f A i p h
    (pullbackExtension f A i p h).f (pullbackExtension f A i p h).g
    (pullbackExtension f A i p h).zero
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app E)
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
      ((etaleAbelianPullbackConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))))
    (pullbackExtension_unit_projection f A i p h)
    (fun U => constantUnit_section f (AddCommGrpCat.of (ULift.{u} ℤ)) U (ULift.up 1))

/-- Pullback of an extension fiber preserves translation by each original
constant coefficient, using the actual constant comparison. -/
theorem pullbackExtensionFiberMap_translation (a : A) :
    constantFiberTranslation A i p h (integerUnitSection Y) a ≫
        pullbackExtensionFiberMap f A i p h =
      pullbackExtensionFiberMap f A i p h ≫
        (etaleSetPushforward f).map
          (constantFiberTranslation A (pullbackExtension f A i p h).f
            (pullbackExtension f A i p h).g (pullbackExtension f A i p h).zero
            (integerUnitSection X) a) :=
  fiberMap_translation f A i p h
    (pullbackExtension f A i p h).f (pullbackExtension f A i p h).g
    (pullbackExtension f A i p h).zero
    ((etaleAbelianPullbackPushforwardAdjunction f).unit.app E)
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
      ((etaleAbelianPullbackConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))))
    (pullbackExtension_unit_projection f A i p h)
    (fun U => constantUnit_section f (AddCommGrpCat.of (ULift.{u} ℤ)) U (ULift.up 1))
    ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _
      ((etaleAbelianPullbackConstantIso f).hom.app A))
    (pullbackExtension_unit_inclusion f A i p h) (constantUnit_section f A) a

end JacobianVarieties.Kummer

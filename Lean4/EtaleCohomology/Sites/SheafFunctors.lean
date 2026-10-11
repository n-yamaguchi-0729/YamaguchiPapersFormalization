/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.BaseChange
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Direct and inverse image of étale coefficient sheaves

Direct image is precomposition with base change on the small étale site.
Inverse image is constructed by restriction to the affine étale site, left Kan
extension, and sheafification. Essential smallness of the affine site supplies
the colimits defining the Kan extension, without enlarging the coefficient universe.

The affine-site comparison transports the Kan-extension adjunction to the
ordinary small étale sites. Exactness of inverse image and the comparison of
geometric stalks are subsequent steps.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]

/-- Direct image of module-valued étale sheaves. -/
def etalePushforward :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u} R) :=
  (etaleBaseChange f).sheafPushforwardContinuous (ModuleCat.{u} R)
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Base change restricted to affine étale objects of the source site. -/
def affineEtaleBaseChange : Y.AffineEtale ⥤ X.Etale :=
  Scheme.AffineEtale.Spec Y ⋙ etaleBaseChange f

instance : (affineEtaleBaseChange f).IsContinuous (Scheme.AffineEtale.topology Y)
    X.smallEtaleTopology :=
  CategoryTheory.Functor.isContinuous_comp (Scheme.AffineEtale.Spec Y) (etaleBaseChange f)
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology

instance (F : Y.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (affineEtaleBaseChange f).op.HasPointwiseLeftKanExtension F := by
  intro U
  let : HasColimitsOfShape (CostructuredArrow (affineEtaleBaseChange f).op U)
      (ModuleCat.{u} R) :=
    hasColimitsOfShape_of_essentiallySmall _ _
  infer_instance

/-- Inverse image, constructed from the affine-site comparison, left Kan extension,
and sheafification. -/
def etalePullback :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  (Scheme.AffineEtale.sheafEquiv Y (ModuleCat.{u} R)).inverse ⋙
    CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
      (affineEtaleBaseChange f) (ModuleCat.{u} R)
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology

private def affineEtalePushforwardIso :
    (affineEtaleBaseChange f).sheafPushforwardContinuous (ModuleCat.{u} R)
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology ≅
      etalePushforward f R ⋙ (Scheme.AffineEtale.sheafEquiv Y (ModuleCat.{u} R)).inverse :=
  (CategoryTheory.Functor.sheafPushforwardContinuousComp
    (Scheme.AffineEtale.Spec Y) (etaleBaseChange f) (ModuleCat.{u} R)
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology).symm

private def affineEtalePushforwardComposeIso :
    (affineEtaleBaseChange f).sheafPushforwardContinuous (ModuleCat.{u} R)
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology ⋙
        (Scheme.AffineEtale.sheafEquiv Y (ModuleCat.{u} R)).functor ≅
      etalePushforward f R :=
  CategoryTheory.Functor.isoWhiskerRight (affineEtalePushforwardIso f R)
      (Scheme.AffineEtale.sheafEquiv Y (ModuleCat.{u} R)).functor ≪≫
    CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (etalePushforward f R)
      (Scheme.AffineEtale.sheafEquiv Y (ModuleCat.{u} R)).counitIso ≪≫
    CategoryTheory.Functor.rightUnitor _

/-- The usual inverse-image/direct-image adjunction on the small étale sites. -/
def etalePullbackPushforwardAdjunction : etalePullback f R ⊣ etalePushforward f R :=
  ((Scheme.AffineEtale.sheafEquiv Y (ModuleCat.{u} R)).symm.toAdjunction.comp
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (affineEtaleBaseChange f) (ModuleCat.{u} R)
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology)).ofNatIsoRight
      (affineEtalePushforwardComposeIso f R)

instance : (etalePullback f R).IsLeftAdjoint :=
  (etalePullbackPushforwardAdjunction f R).isLeftAdjoint

instance : (etalePushforward f R).IsRightAdjoint :=
  (etalePullbackPushforwardAdjunction f R).isRightAdjoint

/-- Sections of direct image are sections on the base-changed étale object. -/
lemma etalePushforward_sections
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (U : Y.Etale) :
    ((etalePushforward f R).obj F).obj.obj (op U) =
      F.obj.obj (op ((etaleBaseChange f).obj U)) := rfl

end EtaleCohomology

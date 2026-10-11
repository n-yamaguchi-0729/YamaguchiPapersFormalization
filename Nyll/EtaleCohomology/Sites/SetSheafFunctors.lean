/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.EtaleCohomology.Sites.ConstantPullback
import Nyll.EtaleCohomology.Sites.Subcanonical
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Yoneda

/-!
# Inverse image of set-valued étale sheaves

The affine étale site supplies the small colimits for inverse image in the
same universe as the values. The resulting functor is left adjoint to
restriction along base change. Constant sheaves are preserved, and inverse
image of the sheaf represented by an étale scheme is represented by its
scheme-theoretic base change.

These constructions apply to arbitrary scheme morphisms and are used to
transfer local splittings of finite étale covers to sheaves of finite sets.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image of sheaves of sets on the small étale sites. -/
def etaleSetPushforward :
    Sheaf X.smallEtaleTopology (Type u) ⥤ Sheaf Y.smallEtaleTopology (Type u) :=
  (etaleBaseChange f).sheafPushforwardContinuous (Type u)
    Y.smallEtaleTopology X.smallEtaleTopology

instance (F : Y.AffineEtaleᵒᵖ ⥤ Type u) :
    (affineEtaleBaseChange f).op.HasPointwiseLeftKanExtension F := by
  intro U
  let : HasColimitsOfShape (CostructuredArrow (affineEtaleBaseChange f).op U) (Type u) :=
    hasColimitsOfShape_of_essentiallySmall _ _
  infer_instance

/-- Inverse image of sheaves of sets, using left Kan extension and sheafification. -/
def etaleSetPullback :
    Sheaf Y.smallEtaleTopology (Type u) ⥤ Sheaf X.smallEtaleTopology (Type u) :=
  (Scheme.AffineEtale.sheafEquiv Y (Type u)).inverse ⋙
    Functor.sheafPullbackConstruction.sheafPullback
      (affineEtaleBaseChange f) (Type u)
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology

private def affineEtaleSetPushforwardComposeIso :
    (affineEtaleBaseChange f).sheafPushforwardContinuous (Type u)
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology ⋙
        (Scheme.AffineEtale.sheafEquiv Y (Type u)).functor ≅
      etaleSetPushforward f :=
  Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp
        (Scheme.AffineEtale.Spec Y) (etaleBaseChange f) (Type u)
        (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology).symm
      (Scheme.AffineEtale.sheafEquiv Y (Type u)).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleSetPushforward f)
      (Scheme.AffineEtale.sheafEquiv Y (Type u)).counitIso ≪≫
    Functor.rightUnitor _

/-- The inverse-image/direct-image adjunction for set-valued étale sheaves. -/
def etaleSetPullbackPushforwardAdjunction : etaleSetPullback f ⊣ etaleSetPushforward f :=
  ((Scheme.AffineEtale.sheafEquiv Y (Type u)).symm.toAdjunction.comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (affineEtaleBaseChange f) (Type u)
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology)).ofNatIsoRight
      (affineEtaleSetPushforwardComposeIso f)

instance : (etaleSetPullback f).IsLeftAdjoint :=
  (etaleSetPullbackPushforwardAdjunction f).isLeftAdjoint

instance : (etaleSetPushforward f).IsRightAdjoint :=
  (etaleSetPullbackPushforwardAdjunction f).isRightAdjoint

/-- Pullback preserves the constant value of a set-valued étale sheaf. -/
def etaleSetPullbackConstantIso :
    constantSheaf Y.smallEtaleTopology (Type u) ⋙ etaleSetPullback f ≅
      constantSheaf X.smallEtaleTopology (Type u) :=
  Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) (Type u)
    terminalIsTerminal (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
    (etaleSetPullback f) (etaleSetPullbackPushforwardAdjunction f)

private def etaleSetPullbackYonedaHomEquiv (U : Y.Etale)
    (G : Sheaf X.smallEtaleTopology (Type u)) :
    ((etaleSetPullback f).obj (Y.smallEtaleTopology.yoneda.obj U) ⟶ G) ≃
      (X.smallEtaleTopology.yoneda.obj ((etaleBaseChange f).obj U) ⟶ G) :=
  ((etaleSetPullbackPushforwardAdjunction f).homEquiv _ G).trans
    (Y.smallEtaleTopology.yonedaEquiv.trans X.smallEtaleTopology.yonedaEquiv.symm)

/-- Inverse image of a represented étale sheaf is represented by the pullback scheme. -/
def etaleSetPullbackYonedaObjIso (U : Y.Etale) :
    (etaleSetPullback f).obj (Y.smallEtaleTopology.yoneda.obj U) ≅
      X.smallEtaleTopology.yoneda.obj ((etaleBaseChange f).obj U) := by
  refine Coyoneda.ext _ _
    (fun {G} a => etaleSetPullbackYonedaHomEquiv f U G a)
    (fun {G} a => (etaleSetPullbackYonedaHomEquiv f U G).symm a)
    (fun a => (etaleSetPullbackYonedaHomEquiv f U _).symm_apply_apply a)
    (fun a => (etaleSetPullbackYonedaHomEquiv f U _).apply_symm_apply a) ?_
  intro G H a b
  change ((etaleSetPullbackPushforwardAdjunction f).homEquiv _ H).symm
      (Y.smallEtaleTopology.yonedaEquiv.symm (X.smallEtaleTopology.yonedaEquiv (a ≫ b))) =
    ((etaleSetPullbackPushforwardAdjunction f).homEquiv _ G).symm
      (Y.smallEtaleTopology.yonedaEquiv.symm (X.smallEtaleTopology.yonedaEquiv a)) ≫ b
  rw [X.smallEtaleTopology.yonedaEquiv_comp]
  exact (congrArg ((etaleSetPullbackPushforwardAdjunction f).homEquiv
      (Y.smallEtaleTopology.yoneda.obj U) H).symm
    (Y.smallEtaleTopology.yonedaEquiv_symm_naturality_right U
      ((etaleSetPushforward f).map b) (X.smallEtaleTopology.yonedaEquiv a)).symm).trans
    ((etaleSetPullbackPushforwardAdjunction f).homEquiv_naturality_right_symm
      (Y.smallEtaleTopology.yonedaEquiv.symm (X.smallEtaleTopology.yonedaEquiv a)) b)

end EtaleCohomology

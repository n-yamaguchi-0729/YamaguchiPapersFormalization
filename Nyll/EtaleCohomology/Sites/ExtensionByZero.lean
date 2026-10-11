/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Extension by zero for an open immersion

Composition with an open immersion gives a fully faithful, continuous inclusion
of small étale sites. Its adjunction with base change identifies restriction of
sheaves with the inverse image constructed in `Sites.SheafFunctors`.

Extension by zero is constructed by passing to the affine étale site, taking
left Kan extension, and sheafifying. The resulting adjunction is with the
existing inverse-image functor. The affine-site comparison supplies the required
small colimits. The stalk formula and exactness are subsequent steps.

Reference: https://stacks.math.columbia.edu/tag/03S2
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Composition with an open immersion on the small étale sites. -/
abbrev openEtaleInclusion : U.Etale ⥤ X.Etale := etalePostcompose j

/-- Composition with the immersion is left adjoint to base change. -/
def openEtaleInclusionBaseChangeAdjunction : openEtaleInclusion j ⊣ etaleBaseChange j :=
  etalePostcomposeBaseChangeAdjunction j

/-- A morphism over the ambient scheme is already over the open subscheme. -/
def openEtaleInclusionFullyFaithful : (openEtaleInclusion j).FullyFaithful where
  preimage {V W} f := (Scheme.Etale.forget U).preimage
    (CategoryTheory.Over.homMk ((Scheme.Etale.forget X).map f).left (by
      apply (cancel_mono j).mp
      exact (Category.assoc _ _ _).trans
        (CategoryTheory.Over.w ((Scheme.Etale.forget X).map f))))
  map_preimage {V W} f := by
    apply (Scheme.Etale.forget X).map_injective
    ext
    exact congrArg
      (fun g : (Scheme.Etale.forget U).obj V ⟶ (Scheme.Etale.forget U).obj W => g.left)
      ((Scheme.Etale.forget U).map_preimage _)
  preimage_map f := (Scheme.Etale.forget U).preimage_map f

instance : (openEtaleInclusion j).Full := (openEtaleInclusionFullyFaithful j).full
instance : (openEtaleInclusion j).Faithful := (openEtaleInclusionFullyFaithful j).faithful

/-- An étale covering over the open subscheme is an étale covering over the ambient scheme. -/
lemma openEtaleInclusion_coverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (openEtaleInclusion j) :=
  etalePostcompose_coverPreserving j

variable (R : Type u) [CommRing R]

/-- Restriction of coefficient sheaves by precomposition with the inclusion of sites. -/
def openEtaleRestriction :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf U.smallEtaleTopology (ModuleCat.{u} R) :=
  (openEtaleInclusion j).sheafPushforwardContinuous (ModuleCat.{u} R)
    U.smallEtaleTopology X.smallEtaleTopology

/-- Restriction is left adjoint to the already constructed direct image. -/
def openEtaleRestrictionPushforwardAdjunction :
    openEtaleRestriction j R ⊣ etalePushforward j R :=
  (openEtaleInclusionBaseChangeAdjunction j).sheafPushforwardContinuous
    U.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image along an open immersion is ordinary restriction of sheaves. -/
def etalePullbackOpenRestrictionIso : etalePullback j R ≅ openEtaleRestriction j R :=
  (etalePullbackPushforwardAdjunction j R).leftAdjointUniq
    (openEtaleRestrictionPushforwardAdjunction j R)

/-- The inclusion restricted to affine étale schemes over the open subscheme. -/
def affineOpenEtaleInclusion : U.AffineEtale ⥤ X.Etale :=
  Scheme.AffineEtale.Spec U ⋙ openEtaleInclusion j

instance : (affineOpenEtaleInclusion j).IsContinuous (Scheme.AffineEtale.topology U)
    X.smallEtaleTopology :=
  CategoryTheory.Functor.isContinuous_comp (Scheme.AffineEtale.Spec U) (openEtaleInclusion j)
    (Scheme.AffineEtale.topology U) U.smallEtaleTopology X.smallEtaleTopology

instance (F : U.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (affineOpenEtaleInclusion j).op.HasPointwiseLeftKanExtension F := by
  intro V
  let : HasColimitsOfShape (CostructuredArrow (affineOpenEtaleInclusion j).op V)
      (ModuleCat.{u} R) :=
    hasColimitsOfShape_of_essentiallySmall _ _
  infer_instance

/-- Extension by zero, constructed by left Kan extension and sheafification. -/
def etaleExtensionByZero :
    Sheaf U.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  (Scheme.AffineEtale.sheafEquiv U (ModuleCat.{u} R)).inverse ⋙
    CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
      (affineOpenEtaleInclusion j) (ModuleCat.{u} R)
      (Scheme.AffineEtale.topology U) X.smallEtaleTopology

private def affineOpenRestrictionIso :
    (affineOpenEtaleInclusion j).sheafPushforwardContinuous (ModuleCat.{u} R)
        (Scheme.AffineEtale.topology U) X.smallEtaleTopology ⋙
      (Scheme.AffineEtale.sheafEquiv U (ModuleCat.{u} R)).functor ≅
      openEtaleRestriction j R :=
  CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.sheafPushforwardContinuousComp
        (Scheme.AffineEtale.Spec U) (openEtaleInclusion j) (ModuleCat.{u} R)
        (Scheme.AffineEtale.topology U) U.smallEtaleTopology X.smallEtaleTopology).symm
      (Scheme.AffineEtale.sheafEquiv U (ModuleCat.{u} R)).functor ≪≫
    CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (openEtaleRestriction j R)
      (Scheme.AffineEtale.sheafEquiv U (ModuleCat.{u} R)).counitIso ≪≫
    CategoryTheory.Functor.rightUnitor _

/-- Extension by zero is left adjoint to inverse image along the open immersion. -/
def etaleExtensionByZeroAdjunction : etaleExtensionByZero j R ⊣ etalePullback j R :=
  (((Scheme.AffineEtale.sheafEquiv U (ModuleCat.{u} R)).symm.toAdjunction.comp
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (affineOpenEtaleInclusion j) (ModuleCat.{u} R)
      (Scheme.AffineEtale.topology U) X.smallEtaleTopology)).ofNatIsoRight
      (affineOpenRestrictionIso j R)).ofNatIsoRight
        (etalePullbackOpenRestrictionIso j R).symm

instance : (etaleExtensionByZero j R).IsLeftAdjoint :=
  (etaleExtensionByZeroAdjunction j R).isLeftAdjoint

instance : (etalePullback j R).IsRightAdjoint :=
  (etaleExtensionByZeroAdjunction j R).isRightAdjoint

end EtaleCohomology

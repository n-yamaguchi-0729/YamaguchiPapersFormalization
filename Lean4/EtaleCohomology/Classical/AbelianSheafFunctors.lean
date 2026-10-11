/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.CoefficientSheaves
import EtaleCohomology.Sites.ClosedImmersionExact
import EtaleCohomology.Sites.PullbackStalks
import EtaleCohomology.Sites.ConstantPullback
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.ULift
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Abelian direct and inverse image on the small étale site

Transport the constructed exact inverse image of integer module sheaves through
the equivalence with abelian sheaves. Direct image is the actual restriction
along étale base change. This connects these functors to mathlib's `Sheaf.H`.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology.Classical

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Integer module sheaves and abelian sheaves have the same objects and maps,
up to the coefficient-category equivalence. -/
def integerSheafEquivalence :
    Sheaf J (ModuleCat.{w} (ULift.{w} ℤ)) ≌ Sheaf J AddCommGrpCat.{w} := by
  let E : ModuleCat.{w} (ULift.{w} ℤ) ≌ AddCommGrpCat.{w} :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv.symm).trans
      (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence
  let : PreservesLimitsOfSize.{v, max u v} E.functor :=
    CategoryTheory.Adjunction.isEquivalencePreservesLimits E.functor
  let : PreservesLimitsOfSize.{v, max u v} E.inverse :=
    CategoryTheory.Adjunction.isEquivalencePreservesLimits E.inverse
  let : J.HasSheafCompose E.functor :=
    hasSheafCompose_of_preservesLimitsOfSize J (F := E.functor)
  let : J.HasSheafCompose E.inverse :=
    hasSheafCompose_of_preservesLimitsOfSize J (F := E.inverse)
  let F := sheafCompose J E.functor
  have : F.EssSurj := ⟨fun G =>
    ⟨(sheafCompose J E.inverse).obj G,
      ⟨(fullyFaithfulSheafToPresheaf J AddCommGrpCat.{w}).preimageIso
        (Functor.associator G.obj E.inverse E.functor ≪≫
          Functor.isoWhiskerLeft G.obj E.counitIso ≪≫ Functor.rightUnitor G.obj)⟩⟩⟩
  let : F.IsEquivalence :=
    { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
  exact F.asEquivalence

end EtaleCohomology.Classical

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image of abelian étale sheaves, by restriction along base change. -/
def etaleAbelianPushforward :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Inverse image of abelian sheaves, using the actual inverse image of integer
module sheaves. -/
def etaleAbelianPullback :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (Classical.integerSheafEquivalence Y.smallEtaleTopology).inverse ⋙
    etalePullback f (ULift.{u} ℤ) ⋙
      (Classical.integerSheafEquivalence X.smallEtaleTopology).functor

private def etaleAbelianPushforwardTransportIso :
    (Classical.integerSheafEquivalence X.smallEtaleTopology).inverse ⋙
        etalePushforward f (ULift.{u} ℤ) ⋙
          (Classical.integerSheafEquivalence Y.smallEtaleTopology).functor ≅
      etaleAbelianPushforward f :=
  Functor.isoWhiskerLeft (Classical.integerSheafEquivalence X.smallEtaleTopology).inverse
      (Iso.refl _ :
        etalePushforward f (ULift.{u} ℤ) ⋙
            (Classical.integerSheafEquivalence Y.smallEtaleTopology).functor ≅
          (Classical.integerSheafEquivalence X.smallEtaleTopology).functor ⋙
            etaleAbelianPushforward f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Classical.integerSheafEquivalence X.smallEtaleTopology).counitIso
      (etaleAbelianPushforward f) ≪≫ Functor.leftUnitor _

/-- The inverse-image/direct-image adjunction for the abelian sheaves used in
classical cohomology. -/
def etaleAbelianPullbackPushforwardAdjunction :
    etaleAbelianPullback f ⊣ etaleAbelianPushforward f :=
  ((Classical.integerSheafEquivalence Y.smallEtaleTopology).symm.toAdjunction.comp
    ((etalePullbackPushforwardAdjunction f (ULift.{u} ℤ)).comp
      (Classical.integerSheafEquivalence X.smallEtaleTopology).toAdjunction)).ofNatIsoRight
    (etaleAbelianPushforwardTransportIso f)

instance : (etaleAbelianPullback f).IsLeftAdjoint :=
  (etaleAbelianPullbackPushforwardAdjunction f).isLeftAdjoint

instance : (etaleAbelianPushforward f).IsRightAdjoint :=
  (etaleAbelianPullbackPushforwardAdjunction f).isRightAdjoint

instance etaleAbelianPullback_preservesFiniteLimits :
    PreservesFiniteLimits (etaleAbelianPullback f) := by
  dsimp only [etaleAbelianPullback]
  infer_instance

instance etaleAbelianPullback_additive : (etaleAbelianPullback f).Additive := by
  let : PreservesBinaryBiproducts (etaleAbelianPullback f) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

instance etaleAbelianPushforward_additive : (etaleAbelianPushforward f).Additive := by
  let : PreservesBinaryBiproducts (etaleAbelianPushforward f) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

instance etaleAbelianPushforwardClosed_preservesFiniteColimits [IsClosedImmersion f] :
    PreservesFiniteColimits (etaleAbelianPushforward f) :=
  preservesFiniteColimits_of_natIso (etaleAbelianPushforwardTransportIso f)

/-- Inverse image preserves the constant abelian sheaves defining `Sheaf.H`. -/
def etaleAbelianPullbackConstantIso :
    constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⋙ etaleAbelianPullback f ≅
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  Sites.constantSheafCompLeftAdjointIso (etaleBaseChange f) AddCommGrpCat.{u}
    terminalIsTerminal (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ Y.Etale))
    (etaleAbelianPullback f) (etaleAbelianPullbackPushforwardAdjunction f)

end EtaleCohomology

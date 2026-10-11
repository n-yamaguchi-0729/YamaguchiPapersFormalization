/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.SheafFunctors
import EtaleCohomology.Sites.SetSheafFunctors
import EtaleCohomology.Sites.PullbackStalks
import EtaleCohomology.Sites.MateComparison
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Underlying set sheaves of étale module sheaves

Forgetting the module structure commutes with constant sheaves, direct image,
and inverse image. The inverse-image comparison is the mate of the identity
between the two direct-image composites. Its invertibility is proved on
geometric stalks using the filtered-colimit comparison for the forgetful
functor and the stalk/skyscraper adjunctions. No field or finiteness assumption
is imposed on the base schemes or the coefficient ring.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
namespace EtaleCohomology
variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- Forget the module structure of an étale sheaf. -/
def etaleModuleUnderlying :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤ Sheaf X.smallEtaleTopology (Type u) :=
  sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} R))

/-- The underlying set sheaf of a constant module sheaf is the constant set sheaf. -/
def etaleConstantModuleUnderlyingIso :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u} R) ⋙ etaleModuleUnderlying X R ≅
      forget (ModuleCat.{u} R) ⋙ constantSheaf X.smallEtaleTopology (Type u) := by
  let : X.smallEtaleTopology.PreservesSheafification (forget (ModuleCat.{u} R)) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget (ModuleCat.{u} R))
  exact constantCommuteCompose X.smallEtaleTopology (forget (ModuleCat.{u} R))

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)
/-- Direct image commutes with forgetting module structure, by restriction of presheaves. -/
def etalePushforwardModuleUnderlyingIso :
    etalePushforward f R ⋙ etaleModuleUnderlying Y R ≅
      etaleModuleUnderlying X R ⋙ etaleSetPushforward f := Iso.refl _

/-- The canonical inverse-image comparison, obtained as the mate of the direct-image identity. -/
def etalePullbackModuleUnderlyingComparison :
    etaleModuleUnderlying Y R ⋙ etaleSetPullback f ⟶
      etalePullback f R ⋙ etaleModuleUnderlying X R :=
  ((mateEquiv (etalePullbackPushforwardAdjunction f R)
    (etaleSetPullbackPushforwardAdjunction f)).symm
      ((etalePushforwardModuleUnderlyingIso R f).hom)).natTrans

end EtaleCohomology

namespace EtaleCohomology.Sites
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{u} J) (R : Type u) [CommRing R]

private def stalkModuleUnderlyingSquare :
    TwoSquare (sheafCompose J (forget (ModuleCat.{u} R)))
      (Φ.sheafFiber (A := ModuleCat.{u} R))
      (Φ.sheafFiber (A := Type u)) (forget (ModuleCat.{u} R)) :=
  (Φ.sheafFiberCompIso (forget (ModuleCat.{u} R))).hom

private def skyscraperModuleUnderlyingSquare :
    TwoSquare (Φ.skyscraperSheafFunctor (A := ModuleCat.{u} R))
      (forget (ModuleCat.{u} R)) (sheafCompose J (forget (ModuleCat.{u} R)))
      (Φ.skyscraperSheafFunctor (A := Type u)) :=
  mateEquiv Φ.skyscraperSheafAdjunction Φ.skyscraperSheafAdjunction
    (stalkModuleUnderlyingSquare Φ R)

private lemma skyscraperModuleUnderlyingSquare_app (M : ModuleCat.{u} R) :
    (skyscraperModuleUnderlyingSquare Φ R).natTrans.app M =
      Φ.skyscraperSheafAdjunction.homEquiv _ _
        ((stalkModuleUnderlyingSquare Φ R).natTrans.app (Φ.skyscraperSheaf M) ≫
          (forget (ModuleCat.{u} R)).map (Φ.skyscraperSheafAdjunction.counit.app M)) := by
  apply (Φ.skyscraperSheafAdjunction.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact mateEquiv_counit Φ.skyscraperSheafAdjunction Φ.skyscraperSheafAdjunction
    (stalkModuleUnderlyingSquare Φ R) M

private lemma skyscraperModuleUnderlyingSquare_app_π
    (M : ModuleCat.{u} R) (V : C) (v : Φ.fiber.obj V) :
    ((skyscraperModuleUnderlyingSquare Φ R).natTrans.app M).hom.app (op V) ≫
        Pi.π (fun _ : Φ.fiber.obj V => (forget (ModuleCat.{u} R)).obj M) v =
      (forget (ModuleCat.{u} R)).map (Pi.π (fun _ : Φ.fiber.obj V => M) v) := by
  rw [skyscraperModuleUnderlyingSquare_app]
  erw [Φ.skyscraperSheafAdjunction_homEquiv_apply_hom]
  change (Φ.skyscraperPresheafHomEquiv
    ((Φ.presheafFiberCompIso (forget (ModuleCat.{u} R))).hom.app
      (Φ.skyscraperPresheaf M) ≫
        (forget (ModuleCat.{u} R)).map (Φ.skyscraperSheafAdjunction.counit.app M))).app
      (op V) ≫ Pi.π _ v = _
  erw [Φ.skyscraperPresheafHomEquiv_app_π]
  change Φ.toPresheafFiber V v ((Φ.skyscraperSheaf M).obj ⋙ forget (ModuleCat.{u} R)) ≫
      ((Φ.presheafFiberCompIso (forget (ModuleCat.{u} R))).hom.app
        (Φ.skyscraperSheaf M).obj ≫
          (forget (ModuleCat.{u} R)).map (Φ.skyscraperSheafAdjunction.counit.app M)) = _
  rw [← Category.assoc, Φ.toPresheafFiber_presheafFiberCompIso_hom_app]
  erw [← Functor.map_comp]
  congr 1
  rw [← Adjunction.homEquiv_symm_id Φ.skyscraperSheafAdjunction M]
  erw [Φ.skyscraperSheafAdjunction_homEquiv_symm_apply]
  exact Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm (𝟙 _) V v

end EtaleCohomology.Sites

namespace EtaleCohomology
open scoped TwoSquare
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

local instance : RepresentablyFlat (etaleBaseChange f) := flat_of_preservesFiniteLimits _

private lemma skyscraperModuleUnderlyingSquare_comap :
    Sites.skyscraperModuleUnderlyingSquare
        ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
          (etaleBaseChange_coverPreserving f)) R =
      (Sites.skyscraperModuleUnderlyingSquare (Scheme.pointSmallEtale s) R) ≫ₕ
        (etalePushforwardModuleUnderlyingIso R f).hom := by
  apply TwoSquare.ext
  intro M
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply Pi.hom_ext
  intro v
  dsimp only [TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    etalePushforwardModuleUnderlyingIso, Iso.refl_hom]
  simp only [Category.id_comp, Category.comp_id]
  exact (Sites.skyscraperModuleUnderlyingSquare_app_π
    ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
      (etaleBaseChange_coverPreserving f)) R M V.unop v).trans
    (Sites.skyscraperModuleUnderlyingSquare_app_π (Scheme.pointSmallEtale s)
      R M ((etaleBaseChange f).obj V.unop) v).symm

/-- The inverse-image comparison is an isomorphism at every geometric point. -/
lemma etalePullbackModuleUnderlyingComparison_stalk_isIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
      ((etalePullbackModuleUnderlyingComparison R f).app F)) := by
  let Φ := Scheme.pointSmallEtale s
  let Ψ := Φ.comap (etaleBaseChange f) (etaleBaseChange_coverPreserving f)
  let adjM := (etalePullbackPushforwardAdjunction f R).comp
    (Φ.skyscraperSheafAdjunction (A := ModuleCat.{u} R))
  let adjT := (etaleSetPullbackPushforwardAdjunction f).comp
    (Φ.skyscraperSheafAdjunction (A := Type u))
  let α : TwoSquare (etaleModuleUnderlying Y R) (etalePullback f R)
      (etaleSetPullback f) (etaleModuleUnderlying X R) :=
    etalePullbackModuleUnderlyingComparison R f
  let β : TwoSquare (etaleModuleUnderlying X R) (Φ.sheafFiber (A := ModuleCat.{u} R))
      (Φ.sheafFiber (A := Type u)) (forget (ModuleCat.{u} R)) :=
    Sites.stalkModuleUnderlyingSquare Φ R
  have hc : IsIso (((mateEquiv adjM adjT).symm
      (Sites.skyscraperModuleUnderlyingSquare Ψ R)).natTrans) := by
    apply (Sites.isIso_inverseMate_iff adjM adjT
      Ψ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
        (Sites.skyscraperModuleUnderlyingSquare Ψ R)).mpr
    change IsIso (((mateEquiv Ψ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction).symm
      (mateEquiv Ψ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
        (Sites.stalkModuleUnderlyingSquare Ψ R))).natTrans)
    rw [Equiv.symm_apply_apply]
    exact inferInstanceAs (IsIso (Ψ.sheafFiberCompIso (forget (ModuleCat.{u} R))).hom)
  have hcomp : (mateEquiv adjM adjT) (α ≫ᵥ β) =
      Sites.skyscraperModuleUnderlyingSquare Ψ R := by
    dsimp only [adjM, adjT]
    rw [mateEquiv_hcomp]
    change (Sites.skyscraperModuleUnderlyingSquare Φ R) ≫ₕ
      (mateEquiv (etalePullbackPushforwardAdjunction f R)
        (etaleSetPullbackPushforwardAdjunction f))
          ((mateEquiv (etalePullbackPushforwardAdjunction f R)
            (etaleSetPullbackPushforwardAdjunction f)).symm
              (etalePushforwardModuleUnderlyingIso R f).hom) = _
    erw [Equiv.apply_symm_apply]
    exact (skyscraperModuleUnderlyingSquare_comap f R s).symm
  have hi : IsIso (α ≫ᵥ β).natTrans := by
    rw [← (mateEquiv adjM adjT).symm_apply_apply (α ≫ᵥ β), hcomp]
    exact hc
  have hcomponent : IsIso (Φ.sheafFiber.map
      ((etalePullbackModuleUnderlyingComparison R f).app F) ≫
        (Φ.sheafFiberCompIso (forget (ModuleCat.{u} R))).hom.app
          ((etalePullback f R).obj F)) := by
    have h := NatIso.isIso_app_of_isIso (α ≫ᵥ β).natTrans F
    change IsIso (Φ.sheafFiber.map (α.natTrans.app F) ≫
      β.natTrans.app ((etalePullback f R).obj F)) at h
    exact h
  exact (isIso_comp_right_iff _
    ((Φ.sheafFiberCompIso (forget (ModuleCat.{u} R))).hom.app
      ((etalePullback f R).obj F))).mp hcomponent

/-- Geometric points detect that inverse image commutes with forgetting module structure. -/
lemma etalePullbackModuleUnderlyingComparison_isIso :
    IsIso (etalePullbackModuleUnderlyingComparison R f) := by
  have : ∀ F, IsIso ((etalePullbackModuleUnderlyingComparison R f).app F) := by
    intro F
    rw [(Scheme.isConservativeFamilyOfPoints_pointSmallEtale'
      X).jointlyReflectIsomorphisms_type.isIso_iff]
    rintro ⟨_, ⟨x⟩⟩
    let sx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
      (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
        ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
    exact etalePullbackModuleUnderlyingComparison_stalk_isIso f R sx F
  exact NatIso.isIso_of_isIso_app _

/-- Underlying set sheaves commute with inverse image for every morphism of schemes. -/
def etalePullbackModuleUnderlyingIso :
    etalePullback f R ⋙ etaleModuleUnderlying X R ≅
      etaleModuleUnderlying Y R ⋙ etaleSetPullback f := by
  have := etalePullbackModuleUnderlyingComparison_isIso f R
  exact (asIso (etalePullbackModuleUnderlyingComparison R f)).symm

end EtaleCohomology

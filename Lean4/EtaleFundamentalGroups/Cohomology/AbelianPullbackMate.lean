/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.AbelianSheafFunctors
import EtaleCohomology.Sites.ModuleSetComparison
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Whiskering

/-!
# Canonical inverse-image comparison for underlying abelian sheaves

This comparison is the mate of the identity between the actual direct-image
functors. Its invertibility is detected on geometric stalks. The mate formula
retains the adjunction compatibility needed to transport constant sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology
variable (X : Scheme.{u})

/-- Forget the abelian group structure of an étale sheaf. -/
private def abelianUnderlying :
    Sheaf X.smallEtaleTopology (AddCommGrpCat.{u}) ⥤ Sheaf X.smallEtaleTopology (Type u) :=
  sheafCompose X.smallEtaleTopology (forget (AddCommGrpCat.{u}))

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)
/-- Direct image commutes with forgetting abelian group structure, by restriction of presheaves. -/
private def abelianPushforwardUnderlyingIso :
    etaleAbelianPushforward f ⋙ abelianUnderlying Y ≅
      abelianUnderlying X ⋙ etaleSetPushforward f := Iso.refl _

/-- The canonical inverse-image comparison, obtained as the mate of the direct-image identity. -/
def abelianPullbackUnderlyingComparison :
    abelianUnderlying Y ⋙ etaleSetPullback f ⟶
      etaleAbelianPullback f ⋙ abelianUnderlying X :=
  ((mateEquiv (etaleAbelianPullbackPushforwardAdjunction f)
    (etaleSetPullbackPushforwardAdjunction f)).symm
      ((abelianPushforwardUnderlyingIso f).hom)).natTrans


/-- The underlying-set comparison respects the actual inverse-image adjunctions. -/
theorem abelianPullbackUnderlyingComparison_homEquiv
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (k : (etaleAbelianPullback f).obj F ⟶ G) :
    (etaleSetPullbackPushforwardAdjunction f).homEquiv _ _
        ((abelianPullbackUnderlyingComparison f).app F ≫
          (abelianUnderlying X).map k) =
      (abelianUnderlying Y).map
        ((etaleAbelianPullbackPushforwardAdjunction f).homEquiv _ _ k) := by
  let adjA := etaleAbelianPullbackPushforwardAdjunction f
  let adjT := etaleSetPullbackPushforwardAdjunction f
  have hu := unit_mateEquiv_symm adjA adjT
    (abelianPushforwardUnderlyingIso f).hom F
  change (abelianUnderlying Y).map (adjA.unit.app F) ≫ 𝟙 _ =
    adjT.unit.app ((abelianUnderlying Y).obj F) ≫
      (etaleSetPushforward f).map ((abelianPullbackUnderlyingComparison f).app F) at hu
  rw [Category.comp_id] at hu
  change adjT.homEquiv ((abelianUnderlying Y).obj F) ((abelianUnderlying X).obj G)
    ((abelianPullbackUnderlyingComparison f).app F ≫ (abelianUnderlying X).map k) =
      (abelianUnderlying Y).map (adjA.homEquiv F G k)
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
    Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

end EtaleFundamentalGroups.Cohomology

namespace EtaleFundamentalGroups.Cohomology.Sites
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  (Φ : GrothendieckTopology.Point.{u} J)

private def stalkAbelianUnderlyingSquare :
    TwoSquare (sheafCompose J (forget (AddCommGrpCat.{u})))
      (Φ.sheafFiber (A := AddCommGrpCat.{u}))
      (Φ.sheafFiber (A := Type u)) (forget (AddCommGrpCat.{u})) :=
  (Φ.sheafFiberCompIso (forget (AddCommGrpCat.{u}))).hom

private def skyscraperAbelianUnderlyingSquare :
    TwoSquare (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{u}))
      (forget (AddCommGrpCat.{u})) (sheafCompose J (forget (AddCommGrpCat.{u})))
      (Φ.skyscraperSheafFunctor (A := Type u)) :=
  mateEquiv Φ.skyscraperSheafAdjunction Φ.skyscraperSheafAdjunction
    (stalkAbelianUnderlyingSquare Φ)

private lemma skyscraperAbelianUnderlyingSquare_app (M : AddCommGrpCat.{u}) :
    (skyscraperAbelianUnderlyingSquare Φ).natTrans.app M =
      Φ.skyscraperSheafAdjunction.homEquiv _ _
        ((stalkAbelianUnderlyingSquare Φ).natTrans.app (Φ.skyscraperSheaf M) ≫
          (forget (AddCommGrpCat.{u})).map (Φ.skyscraperSheafAdjunction.counit.app M)) := by
  apply (Φ.skyscraperSheafAdjunction.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact mateEquiv_counit Φ.skyscraperSheafAdjunction Φ.skyscraperSheafAdjunction
    (stalkAbelianUnderlyingSquare Φ) M

private lemma skyscraperAbelianUnderlyingSquare_app_π
    (M : AddCommGrpCat.{u}) (V : C) (v : Φ.fiber.obj V) :
    ((skyscraperAbelianUnderlyingSquare Φ).natTrans.app M).hom.app (op V) ≫
        Pi.π (fun _ : Φ.fiber.obj V => (forget (AddCommGrpCat.{u})).obj M) v =
      (forget (AddCommGrpCat.{u})).map (Pi.π (fun _ : Φ.fiber.obj V => M) v) := by
  rw [skyscraperAbelianUnderlyingSquare_app]
  erw [Φ.skyscraperSheafAdjunction_homEquiv_apply_hom]
  change (Φ.skyscraperPresheafHomEquiv
    ((Φ.presheafFiberCompIso (forget (AddCommGrpCat.{u}))).hom.app
      (Φ.skyscraperPresheaf M) ≫
        (forget (AddCommGrpCat.{u})).map (Φ.skyscraperSheafAdjunction.counit.app M))).app
      (op V) ≫ Pi.π _ v = _
  erw [Φ.skyscraperPresheafHomEquiv_app_π]
  change Φ.toPresheafFiber V v ((Φ.skyscraperSheaf M).obj ⋙ forget (AddCommGrpCat.{u})) ≫
      ((Φ.presheafFiberCompIso (forget (AddCommGrpCat.{u}))).hom.app
        (Φ.skyscraperSheaf M).obj ≫
          (forget (AddCommGrpCat.{u})).map (Φ.skyscraperSheafAdjunction.counit.app M)) = _
  rw [← Category.assoc, Φ.toPresheafFiber_presheafFiberCompIso_hom_app]
  erw [← Functor.map_comp]
  congr 1
  rw [← Adjunction.homEquiv_symm_id Φ.skyscraperSheafAdjunction M]
  erw [Φ.skyscraperSheafAdjunction_homEquiv_symm_apply]
  exact Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm (𝟙 _) V v

end EtaleFundamentalGroups.Cohomology.Sites

namespace EtaleFundamentalGroups.Cohomology
open scoped TwoSquare
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

local instance : RepresentablyFlat (etaleBaseChange f) := flat_of_preservesFiniteLimits _

private lemma skyscraperAbelianUnderlyingSquare_comap :
    Sites.skyscraperAbelianUnderlyingSquare
        ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
          (etaleBaseChange_coverPreserving f)) =
      (Sites.skyscraperAbelianUnderlyingSquare (Scheme.pointSmallEtale s)) ≫ₕ
        (abelianPushforwardUnderlyingIso f).hom := by
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
    abelianPushforwardUnderlyingIso, Iso.refl_hom]
  simp only [Category.id_comp, Category.comp_id]
  exact (Sites.skyscraperAbelianUnderlyingSquare_app_π
    ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
      (etaleBaseChange_coverPreserving f)) M V.unop v).trans
    (Sites.skyscraperAbelianUnderlyingSquare_app_π (Scheme.pointSmallEtale s)
      M ((etaleBaseChange f).obj V.unop) v).symm

/-- The inverse-image comparison is an isomorphism at every geometric point. -/
lemma abelianPullbackUnderlyingComparison_stalk_isIso
    (F : Sheaf Y.smallEtaleTopology (AddCommGrpCat.{u})) :
    IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
      ((abelianPullbackUnderlyingComparison f).app F)) := by
  let Φ := Scheme.pointSmallEtale s
  let Ψ := Φ.comap (etaleBaseChange f) (etaleBaseChange_coverPreserving f)
  let adjM := (etaleAbelianPullbackPushforwardAdjunction f).comp
    (Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{u}))
  let adjT := (etaleSetPullbackPushforwardAdjunction f).comp
    (Φ.skyscraperSheafAdjunction (A := Type u))
  let α : TwoSquare (abelianUnderlying Y) (etaleAbelianPullback f)
      (etaleSetPullback f) (abelianUnderlying X) :=
    abelianPullbackUnderlyingComparison f
  let β : TwoSquare (abelianUnderlying X) (Φ.sheafFiber (A := AddCommGrpCat.{u}))
      (Φ.sheafFiber (A := Type u)) (forget (AddCommGrpCat.{u})) :=
    Sites.stalkAbelianUnderlyingSquare Φ
  have hc : IsIso (((mateEquiv adjM adjT).symm
      (Sites.skyscraperAbelianUnderlyingSquare Ψ)).natTrans) := by
    apply (EtaleCohomology.Sites.isIso_inverseMate_iff adjM adjT
      Ψ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
        (Sites.skyscraperAbelianUnderlyingSquare Ψ)).mpr
    change IsIso (((mateEquiv Ψ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction).symm
      (mateEquiv Ψ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
        (Sites.stalkAbelianUnderlyingSquare Ψ))).natTrans)
    rw [Equiv.symm_apply_apply]
    exact inferInstanceAs (IsIso (Ψ.sheafFiberCompIso (forget (AddCommGrpCat.{u}))).hom)
  have hcomp : (mateEquiv adjM adjT) (α ≫ᵥ β) =
      Sites.skyscraperAbelianUnderlyingSquare Ψ := by
    dsimp only [adjM, adjT]
    rw [mateEquiv_hcomp]
    change (Sites.skyscraperAbelianUnderlyingSquare Φ) ≫ₕ
      (mateEquiv (etaleAbelianPullbackPushforwardAdjunction f)
        (etaleSetPullbackPushforwardAdjunction f))
          ((mateEquiv (etaleAbelianPullbackPushforwardAdjunction f)
            (etaleSetPullbackPushforwardAdjunction f)).symm
              (abelianPushforwardUnderlyingIso f).hom) = _
    erw [Equiv.apply_symm_apply]
    exact (skyscraperAbelianUnderlyingSquare_comap f s).symm
  have hi : IsIso (α ≫ᵥ β).natTrans := by
    rw [← (mateEquiv adjM adjT).symm_apply_apply (α ≫ᵥ β), hcomp]
    exact hc
  have hcomponent : IsIso (Φ.sheafFiber.map
      ((abelianPullbackUnderlyingComparison f).app F) ≫
        (Φ.sheafFiberCompIso (forget (AddCommGrpCat.{u}))).hom.app
          ((etaleAbelianPullback f).obj F)) := by
    have h := NatIso.isIso_app_of_isIso (α ≫ᵥ β).natTrans F
    change IsIso (Φ.sheafFiber.map (α.natTrans.app F) ≫
      β.natTrans.app ((etaleAbelianPullback f).obj F)) at h
    exact h
  exact (isIso_comp_right_iff _
    ((Φ.sheafFiberCompIso (forget (AddCommGrpCat.{u}))).hom.app
      ((etaleAbelianPullback f).obj F))).mp hcomponent

/-- Geometric points detect that inverse image commutes with forgetting abelian group structure. -/
lemma abelianPullbackUnderlyingComparison_isIso :
    IsIso (abelianPullbackUnderlyingComparison f) := by
  have : ∀ F, IsIso ((abelianPullbackUnderlyingComparison f).app F) := by
    intro F
    rw [(Scheme.isConservativeFamilyOfPoints_pointSmallEtale'
      X).jointlyReflectIsomorphisms_type.isIso_iff]
    rintro ⟨_, ⟨x⟩⟩
    let sx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
      (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
        ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
    exact abelianPullbackUnderlyingComparison_stalk_isIso f sx F
  exact NatIso.isIso_of_isIso_app _

/-- Underlying set sheaves commute with inverse image for every morphism of schemes. -/
def abelianPullbackUnderlyingMateIso :
    etaleAbelianPullback f ⋙ abelianUnderlying X ≅
      abelianUnderlying Y ⋙ etaleSetPullback f := by
  have := abelianPullbackUnderlyingComparison_isIso f
  exact (asIso (abelianPullbackUnderlyingComparison f)).symm

end EtaleFundamentalGroups.Cohomology

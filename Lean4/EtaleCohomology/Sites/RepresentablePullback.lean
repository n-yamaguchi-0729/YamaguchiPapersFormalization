/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.SetSheafFunctors
import EtaleCohomology.Sites.SetPullbackComposition
import EtaleCohomology.Sites.Subcanonical
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.NatIso

/-!
# Natural inverse-image comparison for represented étale sheaves

The existing objectwise isomorphism between the inverse image of a represented
sheaf and the sheaf represented by scheme base change is natural in the
represented object. Its adjoint is the identity section, which also proves
compatibility with composition of base changes. The composition law uses the
already constructed sheaf pullback comparison and the canonical scheme
pullback-pasting isomorphism, without changing either construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
namespace EtaleCohomology
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- Under the inverse-image adjunction, the representable comparison corresponds
to the identity section of the base-changed étale scheme. -/
lemma etaleSetPullbackYonedaObjIso_hom_homEquiv (U : Y.Etale) :
    (etaleSetPullbackPushforwardAdjunction f).homEquiv _ _
        (etaleSetPullbackYonedaObjIso f U).hom =
      Y.smallEtaleTopology.yonedaEquiv.symm (𝟙 ((etaleBaseChange f).obj U)) := by
  change (etaleSetPullbackPushforwardAdjunction f).homEquiv _ _
      (((etaleSetPullbackPushforwardAdjunction f).homEquiv _ _).symm
        (Y.smallEtaleTopology.yonedaEquiv.symm
          (X.smallEtaleTopology.yonedaEquiv (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The adjoint of a morphism after the representable comparison is its Yoneda section. -/
lemma etaleSetPullbackYonedaObjIso_hom_comp_homEquiv (U : Y.Etale)
    (G : Sheaf X.smallEtaleTopology (Type u))
    (k : X.smallEtaleTopology.yoneda.obj ((etaleBaseChange f).obj U) ⟶ G) :
    (etaleSetPullbackPushforwardAdjunction f).homEquiv _ _
        ((etaleSetPullbackYonedaObjIso f U).hom ≫ k) =
      Y.smallEtaleTopology.yonedaEquiv.symm (X.smallEtaleTopology.yonedaEquiv k) := by
  rw [Adjunction.homEquiv_naturality_right, etaleSetPullbackYonedaObjIso_hom_homEquiv]
  exact Y.smallEtaleTopology.yonedaEquiv_symm_naturality_right U
    ((etaleSetPushforward f).map k) (𝟙 ((etaleBaseChange f).obj U))

/-- The existing objectwise comparison is natural in the represented étale scheme. -/
lemma etaleSetPullbackYonedaObjIso_hom_naturality {U V : Y.Etale} (k : U ⟶ V) :
    (etaleSetPullback f).map (Y.smallEtaleTopology.yoneda.map k) ≫
        (etaleSetPullbackYonedaObjIso f V).hom =
      (etaleSetPullbackYonedaObjIso f U).hom ≫
        X.smallEtaleTopology.yoneda.map ((etaleBaseChange f).map k) := by
  apply ((etaleSetPullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    etaleSetPullbackYonedaObjIso_hom_homEquiv, etaleSetPullbackYonedaObjIso_hom_homEquiv]
  erw [Y.smallEtaleTopology.yonedaEquiv_symm_naturality_left,
    Y.smallEtaleTopology.yonedaEquiv_symm_naturality_right]
  congr 1

/-- Inverse image of represented étale sheaves agrees naturally with scheme base change. -/
def etaleSetPullbackYonedaIso :
    Y.smallEtaleTopology.yoneda ⋙ etaleSetPullback f ≅
      etaleBaseChange f ⋙ X.smallEtaleTopology.yoneda :=
  NatIso.ofComponents (etaleSetPullbackYonedaObjIso f)
    (fun k => etaleSetPullbackYonedaObjIso_hom_naturality f k)

/-- The natural comparison retains exactly the previously constructed objectwise isomorphisms. -/
lemma etaleSetPullbackYonedaIso_app (U : Y.Etale) :
    (etaleSetPullbackYonedaIso f).app U = etaleSetPullbackYonedaObjIso f U := rfl

variable (g : Y ⟶ Z)

private lemma pullbackCompIso_hom_homEquiv
    (G : Sheaf Z.smallEtaleTopology (Type u)) (H : Sheaf X.smallEtaleTopology (Type u))
    (k : (etaleSetPullback f).obj ((etaleSetPullback g).obj G) ⟶ H) :
    (etaleSetPullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
        ((etaleSetPullbackCompIso f g).hom.app G ≫ k) =
      (etaleSetPullbackPushforwardAdjunction g).homEquiv _ _
        ((etaleSetPullbackPushforwardAdjunction f).homEquiv _ _ k) ≫
          (etaleSetPushforwardCompIso f g).hom.app H := by
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [etaleSetPullbackCompIso]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

private lemma iteratedYoneda_homEquiv (U : Z.Etale) :
    (etaleSetPullbackPushforwardAdjunction g).homEquiv _ _
      ((etaleSetPullbackPushforwardAdjunction f).homEquiv _ _
        ((etaleSetPullback f).map (etaleSetPullbackYonedaObjIso g U).hom ≫
          (etaleSetPullbackYonedaObjIso f ((etaleBaseChange g).obj U)).hom)) =
      Z.smallEtaleTopology.yonedaEquiv.symm
        (𝟙 ((etaleBaseChange f).obj ((etaleBaseChange g).obj U))) := by
  rw [Adjunction.homEquiv_naturality_left,
    etaleSetPullbackYonedaObjIso_hom_homEquiv]
  erw [etaleSetPullbackYonedaObjIso_hom_comp_homEquiv]
  exact congrArg Z.smallEtaleTopology.yonedaEquiv.symm (Equiv.apply_symm_apply _ _)

private lemma iteratedYoneda_pushforwardComp (U : Z.Etale) :
    Z.smallEtaleTopology.yonedaEquiv.symm
        (𝟙 ((etaleBaseChange f).obj ((etaleBaseChange g).obj U))) ≫
      (etaleSetPushforwardCompIso f g).hom.app
        (X.smallEtaleTopology.yoneda.obj ((etaleBaseChange f).obj ((etaleBaseChange g).obj U))) =
    Z.smallEtaleTopology.yonedaEquiv.symm
      ((MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f g).hom.app U) := by
  erw [Z.smallEtaleTopology.yonedaEquiv_symm_naturality_right]
  congr 1

/-- The representable comparison respects composition: the scheme pullback-pasting
isomorphism agrees with the comparison for sheaf inverse images and the two
successive representable comparisons. -/
lemma etaleSetPullbackYonedaObjIso_comp_hom (U : Z.Etale) :
    (etaleSetPullbackYonedaObjIso (f ≫ g) U).hom ≫
        X.smallEtaleTopology.yoneda.map
          ((MorphismProperty.Over.pullbackComp
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f g).hom.app U) =
      (etaleSetPullbackCompIso f g).hom.app (Z.smallEtaleTopology.yoneda.obj U) ≫
        (etaleSetPullback f).map (etaleSetPullbackYonedaObjIso g U).hom ≫
          (etaleSetPullbackYonedaObjIso f ((etaleBaseChange g).obj U)).hom := by
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f g
  let H := X.smallEtaleTopology.yoneda.obj ((etaleBaseChange f).obj ((etaleBaseChange g).obj U))
  let k : (etaleSetPullback f).obj
      ((etaleSetPullback g).obj (Z.smallEtaleTopology.yoneda.obj U)) ⟶ H :=
    (etaleSetPullback f).map (etaleSetPullbackYonedaObjIso g U).hom ≫
      (etaleSetPullbackYonedaObjIso f ((etaleBaseChange g).obj U)).hom
  apply ((etaleSetPullbackPushforwardAdjunction (f ≫ g)).homEquiv _ H).injective
  have hl := (etaleSetPullbackYonedaObjIso_hom_comp_homEquiv
    (f ≫ g) U H (X.smallEtaleTopology.yoneda.map (e.hom.app U))).trans
      (congrArg Z.smallEtaleTopology.yonedaEquiv.symm
        (X.smallEtaleTopology.yonedaEquiv_yoneda_map (e.hom.app U)))
  have hr := (pullbackCompIso_hom_homEquiv f g
    (Z.smallEtaleTopology.yoneda.obj U) H k).trans
      ((congrArg (fun a => a ≫ (etaleSetPushforwardCompIso f g).hom.app H)
        (iteratedYoneda_homEquiv f g U)).trans (iteratedYoneda_pushforwardComp f g U))
  exact hl.trans hr.symm

end EtaleCohomology

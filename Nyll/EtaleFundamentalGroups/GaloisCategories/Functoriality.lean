/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# Functoriality of automorphism groups of finite fiber functors

Precomposition of a finite-set-valued functor induces a continuous map on its
automorphism groups.  Conjugating by a natural isomorphism is continuous as
well, so the two operations combine into a canonical continuous monoid
homomorphism.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

open _root_.CategoryTheory.Functor

variable {C : Type u₁} [Category.{u₂} C]
variable {C' : Type v₁} [Category.{v₂} C']

/-- Precomposition induces a continuous map on automorphism groups. -/
lemma continuous_mapAut_whiskeringLeft
    (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w}) :
    Continuous (((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F') := by
  rw [Topology.IsInducing.continuous_iff
      (autEmbedding_isClosedEmbedding
        (((whiskeringLeft C C' FintypeCat.{w}).obj H).obj F')).isInducing,
    continuous_pi_iff]
  intro X
  change Continuous fun a ↦ autEmbedding F' a (H.obj X)
  fun_prop

/-- Conjugation by a natural isomorphism is continuous on automorphism groups. -/
lemma continuous_conjAut
    {F G : C ⥤ FintypeCat.{w}} (t : F ≅ G) :
    Continuous t.conjAut := by
  rw [Topology.IsInducing.continuous_iff
      (autEmbedding_isClosedEmbedding G).isInducing,
    continuous_pi_iff]
  intro X
  change Continuous fun a ↦ autEmbedding G (t.conjAut a) X
  suffices (fun a : Aut F ↦ autEmbedding G (t.conjAut a) X) =
      fun a ↦ (t.app X).conjAut (autEmbedding F a X) by
    rw [this]
    fun_prop
  funext a
  apply Iso.ext
  rfl

/--
The continuous homomorphism on automorphism groups induced by precomposition,
then transported along a natural isomorphism.
-/
def autHomOfCompIso
    (H : C ⥤ C') {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F) :
    Aut F' →ₜ* Aut F where
  toMonoidHom :=
    t.conjAut.toMonoidHom.comp
      (((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F')
  continuous_toFun :=
    (continuous_conjAut t).comp (continuous_mapAut_whiskeringLeft H F')

/-- Transport a point backwards through the comparison between a composite
fiber functor and the original fiber functor. -/
def transportedPointOfCompIso
    (H : C ⥤ C') {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F)
    (X : C) (x : F.obj X) : F'.obj (H.obj X) :=
  (t.inv.app X ≫ eqToHom (Functor.comp_obj H F' X)) x

@[simp]
lemma autHomOfCompIso_apply
    (H : C ⥤ C') {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F) (a : Aut F') :
    autHomOfCompIso H t a =
      t.conjAut (((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F' a) :=
  rfl

/-- The stabilizer of a transported point is the inverse image of its original
stabilizer under the homomorphism induced on automorphism groups. -/
theorem stabilizer_transportedPointOfCompIso
    (H : C ⥤ C') {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t : H ⋙ F' ≅ F)
    (X : C) (x : F.obj X) :
    MulAction.stabilizer (Aut F') (transportedPointOfCompIso H t X x) =
      (MulAction.stabilizer (Aut F) x).comap
        (autHomOfCompIso H t).toMonoidHom := by
  dsimp only [transportedPointOfCompIso]
  ext a
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_comap]
  change a.hom.app (H.obj X) ((t.app X).inv x) = (t.app X).inv x ↔
    (t.app X).hom (a.hom.app (H.obj X) ((t.app X).inv x)) = x
  constructor
  · intro ha
    simpa only [Functor.comp_obj, FintypeCat.inv_hom_id_apply] using
      congrArg (fun y ↦ (t.app X).hom y) ha
  · intro ha
    have hinj : Function.Injective
        (fun y : (H ⋙ F').obj X ↦ (t.app X).hom y) := by
      intro y z hyz
      simpa only [FintypeCat.hom_inv_id_apply] using
        congrArg (fun y ↦ (t.app X).inv y) hyz
    apply hinj
    simpa only [FintypeCat.inv_hom_id_apply] using ha

/--
Changing the comparison isomorphism changes the induced homomorphism by
conjugation with the explicit automorphism `t₁.symm ≪≫ t₂`.
-/
@[stacks 0BN5 "changing the fiber-functor comparison conjugates the induced homomorphism"]
theorem autHomOfCompIso_eq_conj
    (H : C ⥤ C') {F : C ⥤ FintypeCat.{w}}
    {F' : C' ⥤ FintypeCat.{w}} (t₁ t₂ : H ⋙ F' ≅ F) (σ : Aut F') :
    autHomOfCompIso H t₂ σ =
      MulAut.conj (G := Aut F) (t₁.symm ≪≫ t₂ : Aut F)
        (autHomOfCompIso H t₁ σ) := by
  change t₂.conjAut
      (((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F' σ) =
    MulAut.conj (G := Aut F) (t₁.symm ≪≫ t₂ : Aut F)
      (t₁.conjAut
        (((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F' σ))
  let τ := ((whiskeringLeft C C' FintypeCat.{w}).obj H).mapAut F' σ
  have conj_eq (a b : Aut F) :
      MulAut.conj (G := Aut F) a b = a.conjAut b := by
    apply Aut.ext
    rfl
  have htrans :
      t₂.conjAut τ =
        (t₁.symm ≪≫ t₂).conjAut (t₁.conjAut τ) := by
    have hcomp : t₁ ≪≫ (t₁.symm ≪≫ t₂) = t₂ := by
      rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
    exact
      (congrArg (fun t : H ⋙ F' ≅ F ↦ t.conjAut τ) hcomp.symm).trans
        (Iso.trans_conjAut t₁ (t₁.symm ≪≫ t₂) τ)
  exact htrans.trans
    (conj_eq (t₁.symm ≪≫ t₂) (t₁.conjAut τ)).symm

/--
The canonical comparison square between the finite continuous-action functors
associated to two fiber functors.
-/
@[stacks 0BTR]
def functorToContActionCompIso
    [GaloisCategory C] [GaloisCategory C']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    H ⋙ functorToContAction F' ≅
      functorToContAction F ⋙
        ContAction.res FintypeCat (autHomOfCompIso H t) :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _
      (Action.mkIso (t.app X) (fun a ↦ by
        change a.hom.app (H.obj X) ≫ (t.app X).hom =
          (t.app X).hom ≫ (autHomOfCompIso H t a).hom.app X
        simp only [autHomOfCompIso_apply, Iso.conjAut_hom,
          Iso.conj_apply, NatTrans.comp_app, Iso.app_hom]
        change a.hom.app (H.obj X) ≫ t.hom.app X =
          t.hom.app X ≫ t.inv.app X ≫
            a.hom.app (H.obj X) ≫ t.hom.app X
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp])))
    (fun {X Y} f ↦ by
      ext : 2
      change (H ⋙ F').map f ≫ t.hom.app Y =
        t.hom.app X ≫ F.map f
      exact t.hom.naturality f)

end CategoryTheory.PreGaloisCategory

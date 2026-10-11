/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Points in pullback fibers

The canonical comparison between a pullback fiber and a composite geometric
fiber is compatible with the first projection of the scheme pullback.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryPullbackFiberPoint (S : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ S) :=
  instCategory S

local instance finiteEtaleHasPullbacksAlongPullbackFiberPoint
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongPullbackFiberPoint
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {X Y : Scheme.{u}} {Omega : Type u} [Field Omega]

/-- The canonical pullback-fiber comparison intertwines the action on the
pulled-back fiber with the induced action on the composite fiber. -/
theorem pullbackFiberIso_hom_fundamentalGroupHom_apply
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X) (a : π₁ᵉᵗ(xi))
    (A : FiniteEtale Y) (y : (fiber xi).obj ((pullback f).obj A)) :
    (pullbackFiberIso f xi).hom.app A
        (a.hom.app ((pullback f).obj A) y) =
      (fundamentalGroupHom f xi a).hom.app A
        ((pullbackFiberIso f xi).hom.app A y) := by
  have h :
      a.hom.app ((pullback f).obj A) ≫ (pullbackFiberIso f xi).hom.app A =
        (pullbackFiberIso f xi).hom.app A ≫
          (fundamentalGroupHom f xi a).hom.app A := by
    simp only [fundamentalGroupHom,
      CategoryTheory.PreGaloisCategory.autHomOfCompIso_apply,
      Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
    simp
    rfl
  exact ConcreteCategory.congr_hom h y

variable [IsSepClosed Omega]


/-- The pullback-fiber comparison sends a lifted point to the composite of
its geometric lift with the first pullback projection. -/
theorem pullbackFiberIso_hom_fiberObjEquivHom_left
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (y : (fiber xi).obj ((pullback f).obj A)) :
    (fiberObjEquivHom (xi ≫ f) A ((pullbackFiberIso f xi).hom.app A y)).left =
      (fiberObjEquivHom xi ((pullback f).obj A) y).left ≫
        Limits.pullback.fst A.hom f := by
  simp only [Over.mk_left, Functor.comp_obj, Functor.id_obj, Functor.const_obj_obj]
  let pc := MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) xi f
  let baseIso : (Over.mk xi).left ≅ Spec (.of Omega) :=
    eqToIso (Over.mk_left xi)
  let : IsFiniteEtale baseIso.hom := by constructor
  let T : FiniteEtale (Spec (.of Omega)) := FiniteEtale.mk baseIso.hom
  let p : T ⟶ (pullback xi).obj ((pullback f).obj A) :=
    (forgetScheme Omega).preimage (FintypeCat.homMk fun _ ↦ y)
  have hpre :
      (forgetScheme Omega).preimage
          (FintypeCat.homMk fun _ ↦ (forgetScheme Omega).map (pc.inv.app A) y) =
        p ≫ pc.inv.app A := by
    apply (forgetScheme Omega).map_injective
    rw [(forgetScheme Omega).map_comp p (pc.inv.app A),
      (forgetScheme Omega).map_preimage
        (FintypeCat.homMk (fun _ : (forgetScheme Omega).obj T ↦
          (forgetScheme Omega).map (pc.inv.app A) y))]
    change (FintypeCat.homMk fun _ ↦ (forgetScheme Omega).map (pc.inv.app A) y) =
      (forgetScheme Omega).map p ≫ (forgetScheme Omega).map (pc.inv.app A)
    rw [show (forgetScheme Omega).map p =
        FintypeCat.homMk (fun _ ↦ y) from (forgetScheme Omega).map_preimage _]
    apply FintypeCat.hom_ext
    intro q
    rfl
  have hpc :
      (pc.inv.app A).left ≫ Limits.pullback.fst A.hom (xi ≫ f) =
        (pc.inv.app A).left ≫ (pc.hom.app A).left ≫
          Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
            Limits.pullback.fst A.hom f := by
    have hcomp :
        (pc.hom.app A).left ≫
            Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
              Limits.pullback.fst A.hom f =
          Limits.pullback.fst A.hom (xi ≫ f) := by
      exact MorphismProperty.Over.pullbackComp_left_fst_fst
        (P := @IsFiniteEtale) (Q := ⊤) xi f A
    rw [← hcomp]
  have hpc' :
      (pc.inv.app A).left ≫ (pc.hom.app A).left ≫
          Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
            Limits.pullback.fst A.hom f =
        Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
          Limits.pullback.fst A.hom f := by
    have hinv : (pc.inv.app A).left ≫ (pc.hom.app A).left = 𝟙 _ := by
      calc
        (pc.inv.app A).left ≫ (pc.hom.app A).left =
            (pc.inv.app A ≫ pc.hom.app A).left := rfl
        _ = (𝟙 ((pullback xi).obj ((pullback f).obj A)) :
              (pullback xi).obj ((pullback f).obj A) ⟶
                (pullback xi).obj ((pullback f).obj A)).left :=
          congrArg (fun k ↦ k.left) (pc.inv_hom_id_app A)
        _ = 𝟙 _ := rfl
    rw [← Category.assoc (pc.inv.app A).left (pc.hom.app A).left, hinv]
    exact Category.id_comp _
  calc
    ((forgetScheme Omega).preimage
        (FintypeCat.homMk fun _ ↦ (forgetScheme Omega).map (pc.inv.app A) y)).left ≫
          Limits.pullback.fst A.hom (xi ≫ f) =
        (p ≫ pc.inv.app A).left ≫
          Limits.pullback.fst A.hom (xi ≫ f) := by rw [hpre]
    _ = p.left ≫ ((pc.inv.app A).left ≫
          Limits.pullback.fst A.hom (xi ≫ f)) := by rfl
    _ = p.left ≫ ((pc.inv.app A).left ≫ (pc.hom.app A).left ≫
          Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
            Limits.pullback.fst A.hom f) := congrArg (fun k ↦ p.left ≫ k) hpc
    _ = p.left ≫ (Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
          Limits.pullback.fst A.hom f) := congrArg (fun k ↦ p.left ≫ k) hpc'
    _ = p.left ≫ Limits.pullback.fst (Limits.pullback.snd A.hom f) xi ≫
          Limits.pullback.fst A.hom f := (Category.assoc _ _ _).symm

end AlgebraicGeometry.FiniteEtale

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.EtaleFundamentalGroups.ContinuousActions.InjectiveRestriction
import Nyll.EtaleFundamentalGroups.GaloisCategories.ConnectedActions
import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality

/-!
# Injectivity of the map attached to a functor of Galois categories

The map on profinite automorphism groups induced by a functor of Galois
categories is injective exactly when every connected target object admits the
epi--mono span of [Stacks Project, Tag 0BN7](https://stacks.math.columbia.edu/tag/0BN7).
-/

noncomputable section

universe u₁ u₂ v₁ v₂ w

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
variable {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']

private theorem categorical_span_of_action_span
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (hspan : ∀ X' : ContAction FintypeCat.{w} (Aut F'),
      Nonempty X'.obj.V →
      MulAction.IsPretransitive (Aut F') X'.obj.V →
      ∃ (X : ContAction FintypeCat.{w} (Aut F))
        (Y' : ContAction FintypeCat.{w} (Aut F'))
        (e : Y' ⟶ X')
        (m : Y' ⟶
          (ContAction.res FintypeCat (autHomOfCompIso H t)).obj X),
        Epi e ∧ Mono m) :
    ∀ X' : C', IsConnected X' →
      ∃ (Y' : C') (X : C) (e : Y' ⟶ X') (m : Y' ⟶ H.obj X),
        Epi e ∧ Mono m := by
  intro X' hconn
  let : IsConnected X' := hconn
  let E := functorToContAction F
  let E' := functorToContAction F'
  let R := ContAction.res FintypeCat (autHomOfCompIso H t)
  have hnon : Nonempty (E'.obj X').obj.V := by
    change Nonempty (F'.obj X')
    infer_instance
  have htrans : MulAction.IsPretransitive (Aut F') (E'.obj X').obj.V := by
    change MulAction.IsPretransitive (Aut F') (F'.obj X')
    infer_instance
  obtain ⟨Z, Y, e, m, he, hm⟩ := hspan (E'.obj X') hnon htrans
  let Y' : C' := E'.objPreimage Y
  let X : C := E.objPreimage Z
  let eY : E'.obj Y' ≅ Y := E'.objObjPreimageIso Y
  let eZ : E.obj X ≅ Z := E.objObjPreimageIso Z
  let s : E'.obj (H.obj X) ≅ R.obj (E.obj X) :=
    (functorToContActionCompIso H t).app X
  let ee : E'.obj Y' ⟶ E'.obj X' := eY.hom ≫ e
  let mm : E'.obj Y' ⟶ E'.obj (H.obj X) :=
    eY.hom ≫ m ≫ (R.mapIso eZ).inv ≫ s.inv
  let ff := Functor.FullyFaithful.ofFullyFaithful E'
  let e' : Y' ⟶ X' := ff.preimage ee
  let m' : Y' ⟶ H.obj X := ff.preimage mm
  have : Epi ee := by
    dsimp [ee]
    infer_instance
  have : Mono mm := by
    dsimp [mm]
    infer_instance
  have hemap : E'.map e' = ee := ff.map_preimage ee
  have hmmap : E'.map m' = mm := ff.map_preimage mm
  have : Epi (E'.map e') := hemap ▸ inferInstance
  have : Mono (E'.map m') := hmmap ▸ inferInstance
  have : Epi e' := E'.epi_of_epi_map inferInstance
  have : Mono m' := E'.mono_of_mono_map inferInstance
  exact ⟨Y', X, e', m', inferInstance, inferInstance⟩

private theorem action_span_of_categorical_span
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (hspan : ∀ X' : C', IsConnected X' →
      ∃ (Y' : C') (X : C) (e : Y' ⟶ X') (m : Y' ⟶ H.obj X),
        Epi e ∧ Mono m) :
    ∀ Z : ContAction FintypeCat.{w} (Aut F'),
      Nonempty Z.obj.V →
      MulAction.IsPretransitive (Aut F') Z.obj.V →
      ∃ (X : ContAction FintypeCat.{w} (Aut F))
        (Y : ContAction FintypeCat.{w} (Aut F'))
        (q : Y ⟶ Z)
        (i : Y ⟶
          (ContAction.res FintypeCat (autHomOfCompIso H t)).obj X),
        Epi q ∧ Mono i := by
  intro Z hnon htrans
  let E := functorToContAction F
  let E' := functorToContAction F'
  let R := ContAction.res FintypeCat (autHomOfCompIso H t)
  let X' : C' := E'.objPreimage Z
  let eZ : E'.obj X' ≅ Z := E'.objObjPreimageIso Z
  let ef :=
    (forget₂ (ContAction FintypeCat (Aut F')) FintypeCat).mapIso eZ
  let : Nonempty (F'.obj X') := ⟨ef.inv hnon.some⟩
  let : MulAction.IsPretransitive (Aut F') (F'.obj X') := by
    constructor
    intro x y
    let zx : Z.obj.V := ef.hom x
    let zy : Z.obj.V := ef.hom y
    obtain ⟨a, ha⟩ := htrans.exists_smul_eq zx zy
    refine ⟨a, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
    have hc := ConcreteCategory.congr_hom (eZ.hom.hom.comm a) x
    change ef.hom (a • x) = a • zx at hc
    exact hc.trans ha
  let : IsConnected X' :=
    FiberFunctor.isConnected_of_isPretransitive F' X'
  obtain ⟨Y', X, q, i, hq, hi⟩ := hspan X' inferInstance
  let : Epi q := hq
  let : Mono i := hi
  let s : E'.obj (H.obj X) ≅ R.obj (E.obj X) :=
    (functorToContActionCompIso H t).app X
  let q' : E'.obj Y' ⟶ Z := E'.map q ≫ eZ.hom
  let i' : E'.obj Y' ⟶ R.obj (E.obj X) := E'.map i ≫ s.hom
  have : Epi (E'.map q) := E'.map_epi q
  have : Mono (E'.map i) := E'.map_mono i
  have : Epi q' := by
    dsimp [q']
    infer_instance
  have : Mono i' := by
    dsimp [i']
    infer_instance
  exact ⟨E.obj X, E'.obj Y', q', i', inferInstance, inferInstance⟩

/--
The homomorphism on profinite automorphism groups induced by `H` and `t` is
injective exactly when every connected object of the target admits an
epimorphism from an object that embeds into an object in the image of `H`.
-/
@[stacks 0BN7]
theorem autHomOfCompIso_injective_iff_exists_epi_mono_span
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    Function.Injective (autHomOfCompIso H t) ↔
      ∀ X' : C', IsConnected X' →
        ∃ (Y' : C') (X : C)
          (q : Y' ⟶ X') (i : Y' ⟶ H.obj X),
          Epi q ∧ Mono i := by
  constructor
  · intro hinj
    exact categorical_span_of_action_span H t
      ((ContAction.injective_iff_exists_epi_mono_span
        (autHomOfCompIso H t)).1 hinj)
  · intro hspan
    apply (ContAction.injective_iff_exists_epi_mono_span
      (autHomOfCompIso H t)).2
    exact action_span_of_categorical_span H t hspan

/-- Restriction of automorphisms along an essentially surjective functor is
injective. No fullness assumption is needed: every target object is already
isomorphic to an object in the image. -/
theorem autHomOfCompIso_injective_of_essSurj
    (H : Functor C C') [H.EssSurj] (t : H ⋙ F' ≅ F) :
    Function.Injective (autHomOfCompIso H t) := by
  rw [autHomOfCompIso_injective_iff_exists_epi_mono_span]
  intro X' _
  let X := H.objPreimage X'
  let e : H.obj X ≅ X' := H.objObjPreimageIso X'
  exact ⟨X', X, 𝟙 X', e.inv, inferInstance, inferInstance⟩

end CategoryTheory.PreGaloisCategory

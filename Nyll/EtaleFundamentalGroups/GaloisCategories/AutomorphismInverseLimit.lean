/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.AutomorphismDescent
import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality
import Nyll.ProCGroups.InverseSystems.Basic
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Automorphism groups of a category assembled from stages

The transition homomorphisms are restriction followed by the specified cone
isomorphism.  Identity and composition follow from ordinary functor coherence.
Joint essential surjectivity and eventual morphism descent make the resulting
continuous comparison bijective.  Compactness then upgrades it to an
isomorphism of topological groups.  No individual restriction or inverse-limit
projection is assumed surjective.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open ProCGroups.InverseSystems

namespace CategoryTheory.PreGaloisCategory

universe u v u' v' w t

variable {I : Type t} [Preorder I]
variable {C : Type u} [Category.{v} C]
variable (Cstage : I → Type u') [∀ i, Category.{v'} (Cstage i)]
variable (H : ∀ i, Cstage i ⥤ C)
variable (T : ∀ {i j : I}, i ≤ j → Cstage i ⥤ Cstage j)
variable (e : ∀ {i j : I} (hij : i ≤ j), H i ≅ T hij ⋙ H j)
variable (F : C ⥤ FintypeCat.{w})

/-- Restriction to the later stage, transported back by the cone comparison. -/
def stageAutRestriction {i j : I} (hij : i ≤ j) :
    Aut (H j ⋙ F) →ₜ* Aut (H i ⋙ F) :=
  autHomOfCompIso (T hij)
    ((isoWhiskerRight (e hij) F ≪≫ Functor.associator (T hij) (H j) F).symm)

/-- The component formula for the constructed transition homomorphism. -/
theorem stageAutRestriction_hom_app {i j : I} (hij : i ≤ j)
    (a : Aut (H j ⋙ F)) (A : Cstage i) :
    (stageAutRestriction Cstage H T e F hij a).hom.app A =
      F.map ((e hij).hom.app A) ≫ a.hom.app ((T hij).obj A) ≫
        F.map ((e hij).inv.app A) := by
  have hw :
      (((whiskeringLeft (Cstage i) (Cstage j) FintypeCat.{w}).obj (T hij)).mapAut
        (H j ⋙ F) a).hom.app A = a.hom.app ((T hij).obj A) := rfl
  simp only [stageAutRestriction, autHomOfCompIso_apply, Iso.conjAut_hom,
    Iso.conj_apply, NatTrans.comp_app, Iso.symm_inv, Iso.symm_hom,
    Iso.trans_hom, Iso.trans_inv, isoWhiskerRight_hom, isoWhiskerRight_inv,
    Functor.associator_hom_app, Functor.associator_inv_app, whiskerRight_app, hw,
    Category.id_comp, Category.comp_id]

/-- The restriction formula expressed as its conjugation square. -/
theorem stageAutRestriction_commutes {i j : I} (hij : i ≤ j)
    (a : Aut (H j ⋙ F)) (A : Cstage i) :
    F.map ((e hij).hom.app A) ≫ a.hom.app ((T hij).obj A) =
      (stageAutRestriction Cstage H T e F hij a).hom.app A ≫
        F.map ((e hij).hom.app A) := by
  have hcancel : F.map ((e hij).inv.app A) ≫ F.map ((e hij).hom.app A) =
      𝟙 (F.obj ((T hij ⋙ H j).obj A)) :=
    (F.mapIso ((e hij).app A)).inv_hom_id
  have hunit : a.hom.app ((T hij).obj A) ≫
      𝟙 (F.obj ((T hij ⋙ H j).obj A)) = a.hom.app ((T hij).obj A) :=
    Category.comp_id (a.hom.app ((T hij).obj A))
  rw [stageAutRestriction_hom_app, Category.assoc, Category.assoc, hcancel, hunit]

variable (d : ∀ i, T (le_rfl : i ≤ i) ≅ 𝟭 (Cstage i))
variable (c : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
  T (hij.trans hjk) ≅ T hij ⋙ T hjk)
variable (he_id : ∀ i,
  e (le_rfl : i ≤ i) ≪≫ isoWhiskerRight (d i) (H i) ≪≫
    Functor.leftUnitor (H i) = Iso.refl (H i))
variable (he_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
  e (hij.trans hjk) ≪≫ isoWhiskerRight (c hij hjk) (H k) ≪≫
      Functor.associator (T hij) (T hjk) (H k) =
    e hij ≪≫ isoWhiskerLeft (T hij) (e hjk))

include he_id in
private theorem cone_identity_component (i : I) (A : Cstage i) :
    (e (le_rfl : i ≤ i)).hom.app A = (H i).map ((d i).inv.app A) := by
  have h := congrArg (fun q : H i ≅ H i ↦ q.hom.app A) (he_id i)
  have hcomp : (e (le_rfl : i ≤ i)).hom.app A ≫
      (H i).map ((d i).hom.app A) = 𝟙 ((H i).obj A) := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      Functor.leftUnitor_hom_app, Iso.refl_hom, NatTrans.id_app,
      whiskerRight_app, Functor.comp_obj, Functor.id_obj, Category.comp_id] using h
  apply (cancel_mono ((H i).map ((d i).hom.app A))).1
  rw [hcomp]
  exact ((H i).mapIso ((d i).app A)).inv_hom_id.symm

include he_comp in
private theorem cone_composition_component {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (A : Cstage i) :
    F.map ((e (hij.trans hjk)).hom.app A) ≫
        F.map ((H k).map ((c hij hjk).hom.app A)) =
      F.map ((e hij).hom.app A) ≫
        F.map ((e hjk).hom.app ((T hij).obj A)) := by
  have h := congrArg
    (fun q : H i ≅ T hij ⋙ T hjk ⋙ H k ↦ q.hom.app A) (he_comp hij hjk)
  have hc : (e (hij.trans hjk)).hom.app A ≫
      (H k).map ((c hij hjk).hom.app A) =
      (e hij).hom.app A ≫ (e hjk).hom.app ((T hij).obj A) := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, Functor.associator_hom_app, whiskerRight_app,
      whiskerLeft_app, Functor.comp_obj, Category.comp_id] using h
  simpa only [F.map_comp] using congrArg F.map hc

include he_id in
/-- Identity refinement induces the identity on the automorphism group. -/
theorem stageAutRestriction_id (i : I) (a : Aut (H i ⋙ F)) :
    stageAutRestriction Cstage H T e F (le_rfl : i ≤ i) a = a := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply (cancel_mono (F.map ((e (le_rfl : i ≤ i)).hom.app A))).1
  rw [← stageAutRestriction_commutes]
  rw [cone_identity_component Cstage H T e d he_id i A]
  exact a.hom.naturality ((d i).inv.app A)

include he_comp in
/-- Composed refinement induces the composite of the constructed restrictions. -/
theorem stageAutRestriction_comp {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (a : Aut (H k ⋙ F)) :
    stageAutRestriction Cstage H T e F hij
        (stageAutRestriction Cstage H T e F hjk a) =
      stageAutRestriction Cstage H T e F (hij.trans hjk) a := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  let Eij := F.map ((e hij).hom.app A)
  let Ejk := F.map ((e hjk).hom.app ((T hij).obj A))
  let Eik := F.map ((e (hij.trans hjk)).hom.app A)
  let Cijk := F.map ((H k).map ((c hij hjk).hom.app A))
  have hc : Eik ≫ Cijk = Eij ≫ Ejk :=
    cone_composition_component Cstage H T e F c he_comp hij hjk A
  have hn : Cijk ≫ a.hom.app ((T hjk).obj ((T hij).obj A)) =
      a.hom.app ((T (hij.trans hjk)).obj A) ≫ Cijk :=
    a.hom.naturality ((c hij hjk).hom.app A)
  apply (cancel_mono (Eij ≫ Ejk)).1
  calc
    (stageAutRestriction Cstage H T e F hij
        (stageAutRestriction Cstage H T e F hjk a)).hom.app A ≫ (Eij ≫ Ejk) =
        Eij ≫ ((stageAutRestriction Cstage H T e F hjk a).hom.app
          ((T hij).obj A) ≫ Ejk) := by
      rw [← Category.assoc, ← stageAutRestriction_commutes, Category.assoc]
    _ = Eij ≫ (Ejk ≫ a.hom.app ((T hjk).obj ((T hij).obj A))) := by
      rw [← stageAutRestriction_commutes]
    _ = (Eik ≫ Cijk) ≫ a.hom.app ((T hjk).obj ((T hij).obj A)) := by
      rw [← Category.assoc, hc]
    _ = Eik ≫ (a.hom.app ((T (hij.trans hjk)).obj A) ≫ Cijk) := by
      rw [Category.assoc, hn]
    _ = (stageAutRestriction Cstage H T e F (hij.trans hjk) a).hom.app A ≫
        (Eik ≫ Cijk) := by
      rw [← Category.assoc, stageAutRestriction_commutes, Category.assoc]
    _ = (stageAutRestriction Cstage H T e F (hij.trans hjk) a).hom.app A ≫
        (Eij ≫ Ejk) := by rw [hc]

/-- The inverse system of actual stage automorphism groups.  Reducibility keeps
the stage group instances definitionally those of the supplied functors. -/
@[reducible] def autInverseSystem : InverseSystem (I := I) where
  X i := Aut (H i ⋙ F)
  topologicalSpace i := inferInstance
  map hij := stageAutRestriction Cstage H T e F hij
  continuous_map hij := (stageAutRestriction Cstage H T e F hij).continuous_toFun
  map_id i := by
    funext a
    exact stageAutRestriction_id Cstage H T e F d he_id i a
  map_comp hij hjk := by
    funext a
    exact stageAutRestriction_comp Cstage H T e F c he_comp hij hjk a

/-- The constructed system is group-valued because its maps are homomorphisms. -/
instance autInverseSystem_isGroupSystem :
    IsGroupSystem (autInverseSystem Cstage H T e F d c he_id he_comp) where
  map_one hij := (stageAutRestriction Cstage H T e F hij).map_one
  map_mul hij a b := (stageAutRestriction Cstage H T e F hij).map_mul a b
  map_inv hij a := (stageAutRestriction Cstage H T e F hij).map_inv a

omit [Preorder I] in
/-- Restriction of a global automorphism to one stage of the cone. -/
def globalAutRestriction (i : I) : Aut F →ₜ* Aut (H i ⋙ F) where
  toMonoidHom := ((Functor.whiskeringLeft (Cstage i) C FintypeCat.{w}).obj (H i)).mapAut F
  continuous_toFun := continuous_mapAut_whiskeringLeft (H i) F

/-- Global restrictions satisfy the compatibility required by the inverse limit. -/
theorem globalAutRestriction_compatible {i j : I} (hij : i ≤ j) (a : Aut F) :
    stageAutRestriction Cstage H T e F hij (globalAutRestriction Cstage H F j a) =
      globalAutRestriction Cstage H F i a := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply (cancel_mono (F.map ((e hij).hom.app A))).1
  rw [← stageAutRestriction_commutes]
  exact a.hom.naturality ((e hij).hom.app A)

/-- The canonical comparison sends a global automorphism to all its restrictions. -/
def autInverseLimitComparison :
    Aut F →ₜ* (autInverseSystem Cstage H T e F d c he_id he_comp).inverseLimit where
  toFun a := ⟨fun i ↦ globalAutRestriction Cstage H F i a, fun i j hij ↦
    globalAutRestriction_compatible Cstage H T e F hij a⟩
  map_one' := by
    apply Subtype.ext
    funext i
    exact (globalAutRestriction Cstage H F i).map_one
  map_mul' a b := by
    apply Subtype.ext
    funext i
    exact (globalAutRestriction Cstage H F i).map_mul a b
  continuous_toFun := Continuous.subtype_mk
    (continuous_pi fun i ↦ (globalAutRestriction Cstage H F i).continuous_toFun)
    (fun a i j hij ↦ globalAutRestriction_compatible Cstage H T e F hij a)

/-- The constructed comparison has the canonical stage coordinate formula. -/
theorem autInverseLimitComparison_projection (i : I) (a : Aut F) :
    (autInverseSystem Cstage H T e F d c he_id he_comp).projection i
        (autInverseLimitComparison Cstage H T e F d c he_id he_comp a) =
      globalAutRestriction Cstage H F i a := rfl

variable (hobj : ∀ X : C, ∃ (i : I) (A : Cstage i), Nonempty ((H i).obj A ≅ X))
variable (hhom : ∀ (i j : I) (A : Cstage i) (B : Cstage j)
  (f : (H i).obj A ⟶ (H j).obj B),
  ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (g : (T hik).obj A ⟶ (T hjk).obj B),
    f = (e hik).hom.app A ≫ (H k).map g ≫ (e hjk).inv.app B)

include hobj in
/-- Joint essential surjectivity detects equality of global automorphisms. -/
theorem autInverseLimitComparison_injective :
    Function.Injective (autInverseLimitComparison Cstage H T e F d c he_id he_comp) := by
  intro a b hab
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨i, A, ⟨q⟩⟩ := hobj X
  have hA : a.hom.app ((H i).obj A) = b.hom.app ((H i).obj A) :=
    congrArg (fun p ↦ (p.val i).hom.app A) hab
  apply (cancel_epi (F.map q.hom)).1
  rw [a.hom.naturality q.hom, b.hom.naturality q.hom, hA]

include hobj hhom in
/-- Eventual morphism descent glues each compatible stage family. -/
theorem autInverseLimitComparison_surjective :
    Function.Surjective (autInverseLimitComparison Cstage H T e F d c he_id he_comp) := by
  intro s
  have hs : ∀ (i j : I) (hij : i ≤ j) (A : Cstage i),
      F.map ((e hij).hom.app A) ≫ (s.val j).hom.app ((T hij).obj A) =
        (s.val i).hom.app A ≫ F.map ((e hij).hom.app A) := by
    intro i j hij A
    have hcompat : stageAutRestriction Cstage H T e F hij (s.val j) = s.val i :=
      s.property i j hij
    rw [stageAutRestriction_commutes, hcompat]
  obtain ⟨a, ha, _⟩ :=
    existsUnique_aut_of_eventualHom Cstage H T e F hobj hhom s.val hs
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext i
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact ha i A

include hobj hhom in
/-- The canonical comparison is bijective under categorical object and morphism descent. -/
theorem autInverseLimitComparison_bijective :
    Function.Bijective (autInverseLimitComparison Cstage H T e F d c he_id he_comp) :=
  ⟨autInverseLimitComparison_injective Cstage H T e F d c he_id he_comp hobj,
    autInverseLimitComparison_surjective Cstage H T e F d c he_id he_comp hobj hhom⟩

/-- Automorphisms of the assembled finite-valued functor form the inverse limit
of its stage automorphism groups, with their canonical topologies. -/
def autInverseLimitEquiv :
    Aut F ≃ₜ* (autInverseSystem Cstage H T e F d c he_id he_comp).inverseLimit :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (autInverseLimitComparison Cstage H T e F d c he_id he_comp).toMonoidHom
    (autInverseLimitComparison Cstage H T e F d c he_id he_comp).continuous_toFun
    (autInverseLimitComparison_bijective Cstage H T e F d c he_id he_comp hobj hhom)

/-- The topological group equivalence retains the original restriction formula. -/
theorem autInverseLimitEquiv_projection (i : I) (a : Aut F) :
    (autInverseSystem Cstage H T e F d c he_id he_comp).projection i
        (autInverseLimitEquiv Cstage H T e F d c he_id he_comp hobj hhom a) =
      globalAutRestriction Cstage H F i a := by
  rw [autInverseLimitEquiv, ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2_apply]
  rfl

end CategoryTheory.PreGaloisCategory

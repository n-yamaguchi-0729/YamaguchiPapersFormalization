/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.PullbackGlobalSectionsComposition
import EtaleCohomology.Sites.PullbackStalkComposition
import EtaleCohomology.Sites.PullbackSections
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# The actual degree-zero Čech section maps

The two projections from a scheme's self-fiber product give section maps
into the same chosen iterated inverse image. Their comparison uses the
existing composition isomorphisms and the actual pullback square equation.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (Λ : Type u) [CommRing Λ]

private def pullback_eq_iso {Z : Scheme.{u}} {f g : Z ⟶ X} (h : f = g) :
    etalePullback f Λ ≅ etalePullback g Λ := by
  cases h
  exact Iso.refl _

/-- The canonical comparison between inverse images along the two
projections of the self-fiber product. -/
def etaleCechPullbackIso :
    etalePullback q Λ ⋙ etalePullback (pullback.fst q q) Λ ≅
      etalePullback q Λ ⋙ etalePullback (pullback.snd q q) Λ :=
  (etalePullbackCompIso (pullback.fst q q) q Λ).symm ≪≫
    pullback_eq_iso Λ (pullback.condition (f := q) (g := q)) ≪≫
    etalePullbackCompIso (pullback.snd q q) q Λ

private lemma sheaf_iso_chain_hom_app_app
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {J : GrothendieckTopology B} {L₀ L₁ L₂ L₃ : A ⥤ Sheaf J C}
    (e₁ : L₀ ≅ L₁) (e : L₀ ≅ L₂) (e₂ : L₂ ≅ L₃) (a : A) (b : Bᵒᵖ) :
    (((e₁.symm ≪≫ e ≪≫ e₂).hom.app a).hom.app b) =
      (e₁.inv.app a).hom.app b ≫ (e.hom.app a).hom.app b ≫
        (e₂.hom.app a).hom.app b := by
  rfl

/-- Evaluation of the actual Čech comparison uses the three individual
comparison maps. The equality is supplied by functoriality of evaluation. -/
theorem etaleCechPullbackIso_hom_app_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((etaleCechPullbackIso q Λ).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback q q)))) =
      ((etalePullbackCompIso (pullback.fst q q) q Λ).inv.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback q q)))) ≫
        ((pullback_eq_iso Λ (pullback.condition (f := q) (g := q))).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback q q)))) ≫
        ((etalePullbackCompIso (pullback.snd q q) q Λ).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback q q)))) := by
  exact sheaf_iso_chain_hom_app_app
    (etalePullbackCompIso (pullback.fst q q) q Λ)
    (pullback_eq_iso Λ (pullback.condition (f := q) (g := q)))
    (etalePullbackCompIso (pullback.snd q q) q Λ) F
    (op (Scheme.Etale.mk (𝟙 (pullback q q))))

/-- The first Čech section map, transported to the second iterated pullback. -/
def etaleCechFirstSectionsMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ⟶
      ((etalePullback (pullback.snd q q) Λ).obj ((etalePullback q Λ).obj F)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback q q)))) :=
  etalePullbackGlobalSectionsMap (pullback.fst q q) Λ ((etalePullback q Λ).obj F) ≫
    ((etaleCechPullbackIso q Λ).hom.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 (pullback q q))))

/-- The second Čech section map. -/
def etaleCechSecondSectionsMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ⟶
      ((etalePullback (pullback.snd q q) Λ).obj ((etalePullback q Λ).obj F)).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback q q)))) :=
  etalePullbackGlobalSectionsMap (pullback.snd q q) Λ ((etalePullback q Λ).obj F)

private lemma globalSectionsMap_eqToIso
    {Z : Scheme.{u}} {f g : Z ⟶ X} (h : f = g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etalePullbackGlobalSectionsMap f Λ F ≫
        ((pullback_eq_iso Λ h).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 Z))) =
      etalePullbackGlobalSectionsMap g Λ F := by
  cases h
  change etalePullbackGlobalSectionsMap f Λ F ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma cech_diagram_condition
    {C : Type*} [Category* C] {A B C₁ C₂ D₁ D₂ : C}
    (a : A ⟶ B) (b₁ : B ⟶ D₁) (b₂ : B ⟶ D₂)
    (c₁ : A ⟶ C₁) (c₂ : A ⟶ C₂)
    (e₁ : C₁ ⟶ D₁) (d₁ : D₁ ⟶ C₁) (e : C₁ ⟶ C₂) (e₂ : C₂ ⟶ D₂)
    (hinv : e₁ ≫ d₁ = 𝟙 C₁)
    (hc₁ : c₁ ≫ e₁ = a ≫ b₁) (hc₂ : c₂ ≫ e₂ = a ≫ b₂)
    (he : c₁ ≫ e = c₂) :
    a ≫ (b₁ ≫ (d₁ ≫ e ≫ e₂)) = a ≫ b₂ := by
  calc
    a ≫ (b₁ ≫ (d₁ ≫ e ≫ e₂)) =
        (c₁ ≫ e₁) ≫ (d₁ ≫ e ≫ e₂) := by rw [← Category.assoc a, ← hc₁]
    _ = (c₁ ≫ e) ≫ e₂ := by
      rw [Category.assoc, ← Category.assoc e₁, hinv, Category.id_comp, ← Category.assoc]
    _ = a ≫ b₂ := by rw [he, hc₂]

/-- The actual global pullback map equalizes the two Čech section maps. -/
theorem etaleCechSections_condition
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etalePullbackGlobalSectionsMap q Λ F ≫ etaleCechFirstSectionsMap q Λ F =
      etalePullbackGlobalSectionsMap q Λ F ≫ etaleCechSecondSectionsMap q Λ F := by
  let W : Scheme.{u} := pullback q q
  let W₀ : W.Etale := Scheme.Etale.mk (𝟙 W)
  let p₁ : W ⟶ Y := pullback.fst q q
  let p₂ : W ⟶ Y := pullback.snd q q
  let h : p₁ ≫ q = p₂ ≫ q := pullback.condition
  let e₁ := ((etalePullbackCompIso p₁ q Λ).hom.app F).hom.app (op W₀)
  let d₁ := ((etalePullbackCompIso p₁ q Λ).inv.app F).hom.app (op W₀)
  let e₂ := ((etalePullbackCompIso p₂ q Λ).hom.app F).hom.app (op W₀)
  let e := ((pullback_eq_iso Λ h).hom.app F).hom.app
    (op W₀)
  let a := etalePullbackGlobalSectionsMap q Λ F
  let b₁ := etalePullbackGlobalSectionsMap p₁ Λ ((etalePullback q Λ).obj F)
  let b₂ := etalePullbackGlobalSectionsMap p₂ Λ ((etalePullback q Λ).obj F)
  let c₁ := etalePullbackGlobalSectionsMap (p₁ ≫ q) Λ F
  let c₂ := etalePullbackGlobalSectionsMap (p₂ ≫ q) Λ F
  have hc₁ : c₁ ≫ e₁ = a ≫ b₁ := etalePullbackGlobalSectionsMap_comp p₁ q Λ F
  have hc₂ : c₂ ≫ e₂ = a ≫ b₂ := etalePullbackGlobalSectionsMap_comp p₂ q Λ F
  have he : c₁ ≫ e = c₂ := globalSectionsMap_eqToIso Λ h F
  have hinv : e₁ ≫ d₁ = 𝟙 _ := congrArg
    (fun k : (etalePullback (p₁ ≫ q) Λ).obj F ⟶ (etalePullback (p₁ ≫ q) Λ).obj F =>
      k.hom.app (op W₀)) ((etalePullbackCompIso p₁ q Λ).hom_inv_id_app F)
  change a ≫ (b₁ ≫ ((etaleCechPullbackIso q Λ).hom.app F).hom.app (op W₀)) = a ≫ b₂
  rw [etaleCechPullbackIso_hom_app_app]
  exact cech_diagram_condition a b₁ b₂ c₁ c₂ e₁ d₁ e e₂ hinv hc₁ hc₂ he

private lemma stalkUnit_eqToIso
    {Z : Scheme.{u}} {f g : Z ⟶ X} (h : f = g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Z // s ≫ f = t})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction f Λ).unit.app F) ≫
      etalePushforwardStalkComponent f t s ((etalePullback f Λ).obj F)) ≫
      (Scheme.pointSmallEtale s.val).sheafFiber.map ((pullback_eq_iso Λ h).hom.app F) =
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction g Λ).unit.app F) ≫
      etalePushforwardStalkComponent g t
        ⟨s.val, by rw [← h]; exact s.property⟩ ((etalePullback g Λ).obj F) := by
  cases h
  let k : (Scheme.pointSmallEtale t).sheafFiber.obj F ⟶
      (Scheme.pointSmallEtale s.val).sheafFiber.obj ((etalePullback f Λ).obj F) :=
    (Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction f Λ).unit.app F) ≫
      etalePushforwardStalkComponent f t s ((etalePullback f Λ).obj F)
  change k ≫ (Scheme.pointSmallEtale s.val).sheafFiber.map (𝟙 _) = k
  rw [(Scheme.pointSmallEtale s.val).sheafFiber.map_id, Category.comp_id]

private lemma iso_chain_hom_app
    {C D : Type*} [Category* C] [Category* D] {F₀ F₁ F₂ F₃ : C ⥤ D}
    (e₁ : F₀ ≅ F₁) (e : F₀ ≅ F₂) (e₂ : F₂ ≅ F₃) (a : C) :
    (e₁.symm ≪≫ e ≪≫ e₂).hom.app a =
      e₁.inv.app a ≫ e.hom.app a ≫ e₂.hom.app a := rfl

/-- The Čech comparison identifies the two composite unit maps on stalks
at any common geometric lift to the self-fiber product. -/
theorem etaleCechPullbackIso_stalk_unit_comp
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s₁ s₂ : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (w : Spec (CommRingCat.of Ω) ⟶ pullback q q)
    (hw₁ : w ≫ pullback.fst q q = s₁.val)
    (hw₂ : w ≫ pullback.snd q q = s₂.val)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₁ ((etalePullback q Λ).obj F)) ≫
      ((Scheme.pointSmallEtale s₁.val).sheafFiber.map
          ((etalePullbackPushforwardAdjunction (pullback.fst q q) Λ).unit.app
            ((etalePullback q Λ).obj F)) ≫
        etalePushforwardStalkComponent (pullback.fst q q) s₁.val ⟨w, hw₁⟩
          ((etalePullback (pullback.fst q q) Λ).obj ((etalePullback q Λ).obj F))) ≫
      (Scheme.pointSmallEtale w).sheafFiber.map ((etaleCechPullbackIso q Λ).hom.app F) =
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₂ ((etalePullback q Λ).obj F)) ≫
      ((Scheme.pointSmallEtale s₂.val).sheafFiber.map
          ((etalePullbackPushforwardAdjunction (pullback.snd q q) Λ).unit.app
            ((etalePullback q Λ).obj F)) ≫
        etalePushforwardStalkComponent (pullback.snd q q) s₂.val ⟨w, hw₂⟩
          ((etalePullback (pullback.snd q q) Λ).obj ((etalePullback q Λ).obj F))) := by
  let p₁ : pullback q q ⟶ Y := pullback.fst q q
  let p₂ : pullback q q ⟶ Y := pullback.snd q q
  let h : p₁ ≫ q = p₂ ≫ q := pullback.condition
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} Λ)
  let S₁ := (Scheme.pointSmallEtale s₁.val).sheafFiber (A := ModuleCat.{u} Λ)
  let S₂ := (Scheme.pointSmallEtale s₂.val).sheafFiber (A := ModuleCat.{u} Λ)
  let W := (Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u} Λ)
  let Fq := (etalePullback q Λ).obj F
  let Fc₁ := (etalePullback (p₁ ≫ q) Λ).obj F
  let Fc₂ := (etalePullback (p₂ ≫ q) Λ).obj F
  let F₁ := (etalePullback p₁ Λ).obj Fq
  let F₂ := (etalePullback p₂ Λ).obj Fq
  let a₁ : T.obj F ⟶ S₁.obj Fq :=
    T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₁ Fq
  let a₂ : T.obj F ⟶ S₂.obj Fq :=
    T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₂ Fq
  let b₁ : S₁.obj Fq ⟶ W.obj F₁ :=
    S₁.map ((etalePullbackPushforwardAdjunction p₁ Λ).unit.app Fq) ≫
      etalePushforwardStalkComponent p₁ s₁.val ⟨w, hw₁⟩ F₁
  let b₂ : S₂.obj Fq ⟶ W.obj F₂ :=
    S₂.map ((etalePullbackPushforwardAdjunction p₂ Λ).unit.app Fq) ≫
      etalePushforwardStalkComponent p₂ s₂.val ⟨w, hw₂⟩ F₂
  let c₁ : T.obj F ⟶ W.obj Fc₁ :=
    T.map ((etalePullbackPushforwardAdjunction (p₁ ≫ q) Λ).unit.app F) ≫
      etalePushforwardStalkComponent (p₁ ≫ q) t
        ⟨w, by rw [← Category.assoc, hw₁]; exact s₁.property⟩ Fc₁
  let c₂ : T.obj F ⟶ W.obj Fc₂ :=
    T.map ((etalePullbackPushforwardAdjunction (p₂ ≫ q) Λ).unit.app F) ≫
      etalePushforwardStalkComponent (p₂ ≫ q) t
        ⟨w, by rw [← Category.assoc, hw₂]; exact s₂.property⟩ Fc₂
  let e₁ : W.obj Fc₁ ⟶ W.obj F₁ := W.map ((etalePullbackCompIso p₁ q Λ).hom.app F)
  let d₁ : W.obj F₁ ⟶ W.obj Fc₁ := W.map ((etalePullbackCompIso p₁ q Λ).inv.app F)
  let e : W.obj Fc₁ ⟶ W.obj Fc₂ := W.map ((pullback_eq_iso Λ h).hom.app F)
  let e₂ : W.obj Fc₂ ⟶ W.obj F₂ := W.map ((etalePullbackCompIso p₂ q Λ).hom.app F)
  have hc₁ : c₁ ≫ e₁ = a₁ ≫ b₁ :=
    etalePullbackUnit_stalkComponent_comp p₁ q t s₁ ⟨w, hw₁⟩ Λ F
  have hc₂ : c₂ ≫ e₂ = a₂ ≫ b₂ :=
    etalePullbackUnit_stalkComponent_comp p₂ q t s₂ ⟨w, hw₂⟩ Λ F
  have he : c₁ ≫ e = c₂ := stalkUnit_eqToIso Λ h t
    ⟨w, by rw [← Category.assoc, hw₁]; exact s₁.property⟩ F
  have hinv : e₁ ≫ d₁ = 𝟙 _ := by
    change W.map _ ≫ W.map _ = _
    rw [← W.map_comp, (etalePullbackCompIso p₁ q Λ).hom_inv_id_app, W.map_id]
  have hchain : W.map ((etaleCechPullbackIso q Λ).hom.app F) = d₁ ≫ e ≫ e₂ := by
    refine (congrArg W.map (iso_chain_hom_app
      (etalePullbackCompIso p₁ q Λ) (pullback_eq_iso Λ h)
      (etalePullbackCompIso p₂ q Λ) F)).trans ?_
    exact (W.map_comp _ _).trans
      (congrArg (fun z => d₁ ≫ z) (W.map_comp _ _))
  change a₁ ≫ b₁ ≫ W.map ((etaleCechPullbackIso q Λ).hom.app F) = a₂ ≫ b₂
  rw [hchain, ← Category.assoc a₁, ← hc₁]
  rw [Category.assoc, ← Category.assoc e₁, hinv, Category.id_comp, ← Category.assoc, he, hc₂]

end EtaleCohomology

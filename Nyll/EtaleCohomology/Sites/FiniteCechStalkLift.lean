/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.CechSections
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.SchemeTheory.Etale.FiniteGeometricPoints
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# A Čech-compatible section determines a germ downstairs

For a finite surjection, lift an algebraically closed geometric point using
the same field. Invert the actual pullback stalk map at one lift. The Čech
equation on the pair of any two lifts shows that this germ works at every
lift, without assuming descent or a stalk-product surjectivity theorem.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem unit_stalkComponent_isIso_of_lift
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) := by
  rcases s with ⟨s, rfl⟩
  exact etalePullbackUnit_stalkComponent_isIso q s Λ F

private theorem globalSectionsMap_germ_of_lift
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etalePullbackGlobalSectionsMap q Λ F ≫
        etaleGlobalSectionsGerm s.val Λ ((etalePullback q Λ).obj F) =
      etaleGlobalSectionsGerm t Λ F ≫
        (Scheme.pointSmallEtale t).sheafFiber.map
          ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
        etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F) := by
  rcases s with ⟨s, rfl⟩
  exact etalePullbackGlobalSectionsMap_germ q s Λ F

/-- Every Čech-compatible global section on a finite surjective pullback
comes from one germ downstairs at each algebraically closed geometric point.
That germ agrees with the section at all lifts with the same field. -/
theorem exists_stalk_lift_of_finite_cech_compatible
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] [Surjective q]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (a : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (ha : etaleCechFirstSectionsMap q Λ F a = etaleCechSecondSectionsMap q Λ F a) :
    ∃ b : ToType ((Scheme.pointSmallEtale t).sheafFiber.obj F),
      ∀ s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t},
        ((Scheme.pointSmallEtale t).sheafFiber.map
            ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
          etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) b =
        etaleGlobalSectionsGerm s.val Λ ((etalePullback q Λ).obj F) a := by
  obtain ⟨y, hy⟩ := q.surjective (t default)
  obtain ⟨s₀, hs₀, _⟩ := q.exists_geometricLift_of_isFinite t y hy
  let s₁ : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t} := ⟨s₀, hs₀⟩
  let Fq := (etalePullback q Λ).obj F
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} Λ)
  let e₁ : T.obj F ⟶ (Scheme.pointSmallEtale s₁.val).sheafFiber.obj Fq :=
    T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₁ Fq
  have : IsIso e₁ := unit_stalkComponent_isIso_of_lift q t s₁ Λ F
  let b : T.obj F := inv e₁ (etaleGlobalSectionsGerm s₁.val Λ Fq a)
  have hb : e₁ b = etaleGlobalSectionsGerm s₁.val Λ Fq a :=
    ConcreteCategory.congr_hom (IsIso.inv_hom_id e₁) _
  refine ⟨b, ?_⟩
  intro s₂
  let W : Scheme.{u} := pullback q q
  let p₁ : W ⟶ Y := pullback.fst q q
  let p₂ : W ⟶ Y := pullback.snd q q
  let w : Spec (CommRingCat.of Ω) ⟶ W :=
    pullback.lift s₁.val s₂.val (s₁.property.trans s₂.property.symm)
  have hw₁ : w ≫ p₁ = s₁.val := pullback.lift_fst _ _ _
  have hw₂ : w ≫ p₂ = s₂.val := pullback.lift_snd _ _ _
  let F₁ := (etalePullback p₁ Λ).obj Fq
  let F₂ := (etalePullback p₂ Λ).obj Fq
  let S₂ := (Scheme.pointSmallEtale s₂.val).sheafFiber (A := ModuleCat.{u} Λ)
  let Ψ := (Scheme.pointSmallEtale w).sheafFiber (A := ModuleCat.{u} Λ)
  let e₂ : T.obj F ⟶ S₂.obj Fq :=
    T.map ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q t s₂ Fq
  let d₁ : (Scheme.pointSmallEtale s₁.val).sheafFiber.obj Fq ⟶ Ψ.obj F₁ :=
    (Scheme.pointSmallEtale s₁.val).sheafFiber.map
        ((etalePullbackPushforwardAdjunction p₁ Λ).unit.app Fq) ≫
      etalePushforwardStalkComponent p₁ s₁.val ⟨w, hw₁⟩ F₁
  let d₂ : S₂.obj Fq ⟶ Ψ.obj F₂ :=
    S₂.map ((etalePullbackPushforwardAdjunction p₂ Λ).unit.app Fq) ≫
      etalePushforwardStalkComponent p₂ s₂.val ⟨w, hw₂⟩ F₂
  let c : F₁ ⟶ F₂ := (etaleCechPullbackIso q Λ).hom.app F
  have : IsIso d₂ := unit_stalkComponent_isIso_of_lift p₂ s₂.val ⟨w, hw₂⟩ Λ Fq
  have hcomp : e₁ ≫ d₁ ≫ Ψ.map c = e₂ ≫ d₂ :=
    etaleCechPullbackIso_stalk_unit_comp q Λ t s₁ s₂ w hw₁ hw₂ F
  have hg₁ : etalePullbackGlobalSectionsMap p₁ Λ Fq ≫ etaleGlobalSectionsGerm w Λ F₁ =
      etaleGlobalSectionsGerm s₁.val Λ Fq ≫ d₁ :=
    globalSectionsMap_germ_of_lift p₁ s₁.val ⟨w, hw₁⟩ Λ Fq
  have hg₂ : etalePullbackGlobalSectionsMap p₂ Λ Fq ≫ etaleGlobalSectionsGerm w Λ F₂ =
      etaleGlobalSectionsGerm s₂.val Λ Fq ≫ d₂ :=
    globalSectionsMap_germ_of_lift p₂ s₂.val ⟨w, hw₂⟩ Λ Fq
  have hn : c.hom.app (op (Scheme.Etale.mk (𝟙 W))) ≫ etaleGlobalSectionsGerm w Λ F₂ =
      etaleGlobalSectionsGerm w Λ F₁ ≫ Ψ.map c :=
    ((Scheme.pointSmallEtale w).toPresheafFiber_naturality c.hom
      (Scheme.Etale.mk (𝟙 W)) (Over.homMk w (Category.comp_id w))).symm
  have hfirst : etaleCechFirstSectionsMap q Λ F ≫ etaleGlobalSectionsGerm w Λ F₂ =
      (etaleGlobalSectionsGerm s₁.val Λ Fq ≫ d₁) ≫ Ψ.map c := by
    change (etalePullbackGlobalSectionsMap p₁ Λ Fq ≫ c.hom.app _) ≫ _ = _
    rw [Category.assoc, hn, ← Category.assoc, hg₁]
  have hg : Ψ.map c (d₁ (etaleGlobalSectionsGerm s₁.val Λ Fq a)) =
      d₂ (etaleGlobalSectionsGerm s₂.val Λ Fq a) :=
    (ConcreteCategory.congr_hom hfirst a).symm.trans
      ((congrArg (etaleGlobalSectionsGerm w Λ F₂) ha).trans
        (ConcreteCategory.congr_hom hg₂ a))
  change e₂ b = _
  apply (ModuleCat.mono_iff_injective d₂).mp inferInstance
  exact (ConcreteCategory.congr_hom hcomp b).symm.trans
    ((congrArg (fun z => Ψ.map c (d₁ z)) hb).trans hg)

end EtaleCohomology

/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.PullbackSections
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Composition of actual inverse-image maps on global sections

The chosen inverse images compose through the existing adjoint-uniqueness
isomorphism. Evaluating its unit equation and the actual base-change maps
at identity objects proves the corresponding equation on global sections.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X)
variable (Λ : Type u) [CommRing Λ]

/-- The actual inverse-image composition comparison intertwines the two adjunction units. -/
lemma etalePullbackComp_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etalePullbackPushforwardAdjunction (p ≫ q) Λ).unit.app F ≫
        (etalePushforward (p ≫ q) Λ).map ((etalePullbackCompIso p q Λ).hom.app F) =
      ((etalePullbackPushforwardAdjunction q Λ).unit.app F ≫
        (etalePushforward q Λ).map ((etalePullbackPushforwardAdjunction p Λ).unit.app
          ((etalePullback q Λ).obj F))) ≫
        (etalePushforwardCompIso p q Λ).hom.app
          ((etalePullback p Λ).obj ((etalePullback q Λ).obj F)) := by
  let a := etalePullbackPushforwardAdjunction (p ≫ q) Λ
  let b := (etalePullbackPushforwardAdjunction q Λ).comp
    (etalePullbackPushforwardAdjunction p Λ)
  let e := etalePushforwardCompIso p q Λ
  have h := Adjunction.unit_leftAdjointUniq_hom_app a (b.ofNatIsoRight e) F
  change a.unit.app F ≫ (etalePushforward (p ≫ q) Λ).map
      ((etalePullbackCompIso p q Λ).hom.app F) = b.unit.app F ≫
        e.hom.app ((etalePullback p Λ).obj ((etalePullback q Λ).obj F)) at h
  rw [Adjunction.comp_unit_app] at h
  exact h

/-- Pulling a global section twice equals pulling it along the composite,
under the existing canonical composition isomorphism of inverse images. -/
theorem etalePullbackGlobalSectionsMap_comp
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etalePullbackGlobalSectionsMap (p ≫ q) Λ F ≫
        ((etalePullbackCompIso p q Λ).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 Z))) =
      etalePullbackGlobalSectionsMap q Λ F ≫
        etalePullbackGlobalSectionsMap p Λ ((etalePullback q Λ).obj F) := by
  let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  let Y₀ : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let Z₀ : Z.Etale := Scheme.Etale.mk (𝟙 Z)
  let Wq : Y.Etale := (etaleBaseChange q).obj X₀
  let Wp : Z.Etale := (etaleBaseChange p).obj Y₀
  let Wc : Z.Etale := (etaleBaseChange (p ≫ q)).obj X₀
  let Wpq : Z.Etale := (etaleBaseChange p).obj Wq
  let aq : Y₀ ⟶ Wq :=
    etaleBaseChangeLift q q ((Category.comp_id q).trans (Category.id_comp q).symm)
  let ap : Z₀ ⟶ Wp :=
    etaleBaseChangeLift p p ((Category.comp_id p).trans (Category.id_comp p).symm)
  let ac : Z₀ ⟶ Wc := etaleBaseChangeLift (p ≫ q) (p ≫ q)
    ((Category.comp_id (p ≫ q)).trans (Category.id_comp (p ≫ q)).symm)
  let c : Wc ⟶ Wpq :=
    (MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) p q).hom.app X₀
  let d : Wp ⟶ Wpq := (etaleBaseChange p).map aq
  have hac : ac ≫ c = ap ≫ d := by
    have : IsIso Wq.hom := inferInstanceAs (IsIso (pullback.snd (𝟙 X) q))
    have : IsIso Wpq.hom := inferInstanceAs (IsIso (pullback.snd Wq.hom p))
    let k₁ : Z₀ ⟶ Wpq := ac ≫ c
    let k₂ : Z₀ ⟶ Wpq := ap ≫ d
    change k₁ = k₂
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono Wpq.hom).mp
    exact k₁.w.trans k₂.w.symm
  let Fq := (etalePullback q Λ).obj F
  let Fc := (etalePullback (p ≫ q) Λ).obj F
  let Fpq := (etalePullback p Λ).obj Fq
  let A := F.obj.obj (op X₀)
  let Pq : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := Fq.obj
  let Pc : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := Fc.obj
  let Ppq : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := Fpq.obj
  let e : Pc ⟶ Ppq := ((etalePullbackCompIso p q Λ).hom.app F).hom
  let uq : A ⟶ Pq.obj (op Wq) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app (op X₀)
  let uc : A ⟶ Pc.obj (op Wc) :=
    ((etalePullbackPushforwardAdjunction (p ≫ q) Λ).unit.app F).hom.app (op X₀)
  let up : Pq.obj (op Y₀) ⟶ Ppq.obj (op Wp) :=
    ((etalePullbackPushforwardAdjunction p Λ).unit.app Fq).hom.app (op Y₀)
  let upq : Pq.obj (op Wq) ⟶ Ppq.obj (op Wpq) :=
    ((etalePullbackPushforwardAdjunction p Λ).unit.app Fq).hom.app (op Wq)
  let rq : Pq.obj (op Wq) ⟶ Pq.obj (op Y₀) := Pq.map aq.op
  let rp : Ppq.obj (op Wp) ⟶ Ppq.obj (op Z₀) := Ppq.map ap.op
  let rc : Pc.obj (op Wc) ⟶ Pc.obj (op Z₀) := Pc.map ac.op
  let rcpq : Ppq.obj (op Wc) ⟶ Ppq.obj (op Z₀) := Ppq.map ac.op
  let hc : Ppq.obj (op Wpq) ⟶ Ppq.obj (op Wc) := Ppq.map c.op
  let hd : Ppq.obj (op Wpq) ⟶ Ppq.obj (op Wp) := Ppq.map d.op
  let ec : Pc.obj (op Wc) ⟶ Ppq.obj (op Wc) := e.app (op Wc)
  let e₀ : Pc.obj (op Z₀) ⟶ Ppq.obj (op Z₀) := e.app (op Z₀)
  have he : rc ≫ e₀ = ec ≫ rcpq := e.naturality ac.op
  have hp : rq ≫ up = upq ≫ hd :=
    ((etalePullbackPushforwardAdjunction p Λ).unit.app Fq).hom.naturality aq.op
  have hmap : hc ≫ rcpq = hd ≫ rp := by
    calc
      hc ≫ rcpq = Ppq.map (ac ≫ c).op := (Ppq.map_comp c.op ac.op).symm
      _ = Ppq.map (ap ≫ d).op := congrArg (fun k : Z₀ ⟶ Wpq => Ppq.map k.op) hac
      _ = hd ≫ rp := Ppq.map_comp d.op ap.op
  have hu : uc ≫ ec = (uq ≫ upq) ≫ hc := by
    have h := congrArg
      (fun k : F ⟶ (etalePushforward (p ≫ q) Λ).obj Fpq => k.hom.app (op X₀))
      (etalePullbackComp_unit p q Λ F)
    change uc ≫ ec = (uq ≫ upq) ≫ (𝟙 _ ≫ hc) at h
    exact h.trans (congrArg (fun k => (uq ≫ upq) ≫ k) (Category.id_comp hc))
  change (uc ≫ rc) ≫ e₀ = (uq ≫ rq) ≫ (up ≫ rp)
  calc
    (uc ≫ rc) ≫ e₀ = (uc ≫ ec) ≫ rcpq := by
      rw [Category.assoc, he, ← Category.assoc]
    _ = (uq ≫ upq) ≫ (hc ≫ rcpq) := by rw [hu, Category.assoc]
    _ = (uq ≫ upq) ≫ (hd ≫ rp) := congrArg (fun k => (uq ≫ upq) ≫ k) hmap
    _ = (uq ≫ (upq ≫ hd)) ≫ rp := by simp only [Category.assoc]
    _ = (uq ≫ (rq ≫ up)) ≫ rp := by rw [← hp]
    _ = (uq ≫ rq) ≫ (up ≫ rp) := by simp only [Category.assoc]

end EtaleCohomology

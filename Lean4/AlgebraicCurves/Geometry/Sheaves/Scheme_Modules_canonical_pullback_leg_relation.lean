/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

The prescribed module pseudofunctor is fixed throughout. Native category,
object and Iso.hom projections are set while all scheme maps remain abstract.
The mathematical overlap law is the existing canonical descent comparison.
-/
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_toDescentData_map_bijective_of_openCover
import SchemeTheory.CategoryTheory.DescentComparison

/-!
Canonical pullback transitions and their comparison with the prescribed descent data.
All scheme maps and module objects retain their original canonical owners.
-/

universe t u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_toDescentData_map_bijective_of_openCover.AlgebraicGeometry.Scheme.Modules.HomZar

namespace AlgebraicCurves.Geometry.Sheaves.DescentComparison

/-- The prescribed canonical transition, with native module objects fixed
before any geometric pullback schemes are substituted. -/
noncomputable def canonicalTransition
    {S X₁ X₂ Y : Scheme.{u}}
    (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (d : Y ⟶ S)
    (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂)
    (e₁ : a₁ ≫ q₁ = d) (e₂ : a₂ ≫ q₂ = d) (L : S.Modules) :
    (Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback q₁).obj L) ⟶
      (Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback q₂).obj L) :=
  (Mdl.mapComp' q₁.op.toLoc a₁.op.toLoc d.op.toLoc
    (by rw [← e₁]; rfl)).inv.toNatTrans.app L ≫
  (Mdl.mapComp' q₂.op.toLoc a₂.op.toLoc d.op.toLoc
    (by rw [← e₂]; rfl)).hom.toNatTrans.app L

/-- The native canonical transition is the original four-factor transition. -/
theorem canonicalTransition_eq_fourfold
    {S X₁ X₂ Y : Scheme.{u}}
    (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (d : Y ⟶ S)
    (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂)
    (e₁ : a₁ ≫ q₁ = d) (e₂ : a₂ ≫ q₂ = d) (L : S.Modules) :
    canonicalTransition q₁ q₂ d a₁ a₂ e₁ e₂ L =
      (Scheme.Modules.pullbackComp a₁ q₁).hom.app L ≫
      (Scheme.Modules.pullbackCongr e₁).hom.app L ≫
      (Scheme.Modules.pullbackCongr e₂.symm).hom.app L ≫
      (Scheme.Modules.pullbackComp a₂ q₂).inv.app L := by
  have ha := Mdl_mapComp'_inv_app a₁ q₁ L d e₁
  have hb := Mdl_mapComp'_hom_app a₂ q₂ L d e₂
  have hab := congrArg₂
    (fun (x : (Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback q₁).obj L) ⟶
        (Scheme.Modules.pullback d).obj L)
      (y : (Scheme.Modules.pullback d).obj L ⟶
        (Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback q₂).obj L)) => x ≫ y) ha hb
  exact hab.trans (Category.assoc _ _ _)

/-- Expose only the prescribed transition value in its native Hom type. -/
theorem canonicalTransition_eq_prescribed
    {S X₁ X₂ Y : Scheme.{u}}
    (q₁ : X₁ ⟶ S) (q₂ : X₂ ⟶ S) (d : Y ⟶ S)
    (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂)
    (e₁ : a₁ ≫ q₁ = d) (e₂ : a₂ ≫ q₂ = d) (L : S.Modules) :
    canonicalTransition q₁ q₂ d a₁ a₂ e₁ e₂ L =
      (Mdl.mapComp' q₁.op.toLoc a₁.op.toLoc d.op.toLoc
        (by rw [← e₁]; rfl)).inv.toNatTrans.app L ≫
      (Mdl.mapComp' q₂.op.toLoc a₂.op.toLoc d.op.toLoc
        (by rw [← e₂]; rfl)).hom.toNatTrans.app L := rfl

/-- Identify the prescribed square component in a fixed native module category. -/
theorem square_component_eq
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Z)
    (h : W ⟶ Y) (k : Y ⟶ Z) (e : f ≫ g = h ≫ k) (L : Z.Modules) :
    Eq (α := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅
      (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback k).obj L))
      ((Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk e).op.toLoc)).symm.app L)
      ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr e ≪≫
        (Scheme.Modules.pullbackComp h k).symm).app L) := by
  apply Iso.ext
  have hc :
      (Mdl.isoMapOfCommSq (CommSq.mk e).op.toLoc).inv.toNatTrans.app L =
        (Mdl.mapComp' g.op.toLoc f.op.toLoc (h ≫ k).op.toLoc
          (by rw [← e]; rfl)).inv.toNatTrans.app L ≫
        (Mdl.mapComp' k.op.toLoc h.op.toLoc (h ≫ k).op.toLoc rfl).hom.toNatTrans.app L := by
    rw [Mdl.isoMapOfCommSq_eq (CommSq.mk e).op.toLoc (h ≫ k).op.toLoc rfl]
    rfl
  have ha := Mdl_mapComp'_inv_app f g L (h ≫ k) e
  have hb := Mdl_mapComp'_hom_app h k L (h ≫ k) rfl
  have hb' : (Mdl.mapComp' k.op.toLoc h.op.toLoc (h ≫ k).op.toLoc rfl).hom.toNatTrans.app L =
      (Scheme.Modules.pullbackComp h k).inv.app L :=
    hb.trans (Category.id_comp _)
  have hab := congrArg₂
    (fun (x : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ⟶
        (Scheme.Modules.pullback (h ≫ k)).obj L)
      (y : (Scheme.Modules.pullback (h ≫ k)).obj L ⟶
        (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback k).obj L)) => x ≫ y) ha hb'
  exact hc.trans (hab.trans (Category.assoc _ _ _))

/-- Identify the prescribed composition component in the native module category. -/
theorem composition_component_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : X ⟶ Z) (e : f ≫ g = m) (L : Z.Modules) :
    Eq (α := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅
      (Scheme.Modules.pullback m).obj L)
      ((Cat.Hom.toNatIso (Mdl.mapComp' g.op.toLoc f.op.toLoc m.op.toLoc
        (by rw [← e]; rfl))).symm.app L)
      ((Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr e).app L) := by
  apply Iso.ext
  exact Mdl_mapComp'_inv_app f g L m e

/-- Canonical overlap coherence in the native module categories.
Every commutative square is supplied by the original geometric maps. -/
theorem prescribed_pullback_leg_relation
    {ι : Type t} {S S' : Scheme.{u}} {X X' : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (f' : ∀ i, X' i ⟶ S')
    (p : S' ⟶ S) (p' : ∀ i, X' i ⟶ X i)
    (w : ∀ i, p' i ≫ f i = f' i ≫ p)
    (M : S.Modules)
    {Y V : Scheme.{u}} (d : Y ⟶ S) (m : V ⟶ S') (s : V ⟶ Y)
    (i j : ι) (a₁ : Y ⟶ X i) (a₂ : Y ⟶ X j)
    (r₁ : V ⟶ X' i) (r₂ : V ⟶ X' j)
    (e₁ : a₁ ≫ f i = d) (e₂ : a₂ ≫ f j = d)
    (G₁ : r₁ ≫ f' i = m) (G₂ : r₂ ≫ f' j = m)
    (E₁ : s ≫ a₁ = r₁ ≫ p' i) (E₂ : s ≫ a₂ = r₂ ≫ p' j)
    (hq : s ≫ d = m ≫ p) :
    let N :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ⟶
          (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) :=
      (Scheme.Modules.pullback s).map
        ((Mdl.mapComp' (f i).op.toLoc a₁.op.toLoc d.op.toLoc
          (by rw [← e₁]; rfl)).inv.toNatTrans.app M ≫
         (Mdl.mapComp' (f j).op.toLoc a₂.op.toLoc d.op.toLoc
          (by rw [← e₂]; rfl)).hom.toNatTrans.app M)
    let C₁ :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ≅
          (Scheme.Modules.pullback r₁).obj
            ((Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M)) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk E₁).op.toLoc)).symm.app
        ((Scheme.Modules.pullback (f i)).obj M)
    let C₂ :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) ≅
          (Scheme.Modules.pullback r₂).obj
            ((Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M)) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk E₂).op.toLoc)).symm.app
        ((Scheme.Modules.pullback (f j)).obj M)
    let K₁ :
        (Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M) ≅
          (Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M
    let K₂ :
        (Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M) ≅
          (Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk (w j)).op.toLoc)).symm.app M
    let T₁ :
        (Scheme.Modules.pullback r₁).obj
            ((Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M)) ≅
          (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.mapComp' (f' i).op.toLoc r₁.op.toLoc
        m.op.toLoc (by rw [← G₁]; rfl))).symm.app ((Scheme.Modules.pullback p).obj M)
    let T₂ :
        (Scheme.Modules.pullback r₂).obj
            ((Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M)) ≅
          (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.mapComp' (f' j).op.toLoc r₂.op.toLoc
        m.op.toLoc (by rw [← G₂]; rfl))).symm.app ((Scheme.Modules.pullback p).obj M)
    N ≫ (C₂ ≪≫ (Scheme.Modules.pullback r₂).mapIso K₂ ≪≫ T₂).hom =
      (C₁ ≪≫ (Scheme.Modules.pullback r₁).mapIso K₁ ≪≫ T₁).hom := by
  exact CategoryTheory.Pseudofunctor.DescentComparison.canonical_pullback_leg_relation
    Mdl f f' p p' w M d m s i j a₁ a₂ r₁ r₂ e₁ e₂ G₁ G₂ E₁ E₂ hq

/-- Canonical overlap coherence in the native module categories.
Every commutative square is supplied by the original geometric maps. -/
theorem canonical_pullback_leg_relation
    {ι : Type t} {S S' : Scheme.{u}} {X X' : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (f' : ∀ i, X' i ⟶ S')
    (p : S' ⟶ S) (p' : ∀ i, X' i ⟶ X i)
    (w : ∀ i, p' i ≫ f i = f' i ≫ p)
    (M : S.Modules)
    {Y V : Scheme.{u}} (d : Y ⟶ S) (m : V ⟶ S') (s : V ⟶ Y)
    (i j : ι) (a₁ : Y ⟶ X i) (a₂ : Y ⟶ X j)
    (r₁ : V ⟶ X' i) (r₂ : V ⟶ X' j)
    (e₁ : a₁ ≫ f i = d) (e₂ : a₂ ≫ f j = d)
    (G₁ : r₁ ≫ f' i = m) (G₂ : r₂ ≫ f' j = m)
    (E₁ : s ≫ a₁ = r₁ ≫ p' i) (E₂ : s ≫ a₂ = r₂ ≫ p' j)
    (hq : s ≫ d = m ≫ p) :
    let N :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ⟶
          (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) :=
      (Scheme.Modules.pullback s).map
        (canonicalTransition (f i) (f j) d a₁ a₂ e₁ e₂ M)
    let C₁ :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ≅
          (Scheme.Modules.pullback r₁).obj
            ((Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M)) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk E₁).op.toLoc)).symm.app
        ((Scheme.Modules.pullback (f i)).obj M)
    let C₂ :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) ≅
          (Scheme.Modules.pullback r₂).obj
            ((Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M)) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk E₂).op.toLoc)).symm.app
        ((Scheme.Modules.pullback (f j)).obj M)
    let K₁ :
        (Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M) ≅
          (Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M
    let K₂ :
        (Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M) ≅
          (Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.isoMapOfCommSq (CommSq.mk (w j)).op.toLoc)).symm.app M
    let T₁ :
        (Scheme.Modules.pullback r₁).obj
            ((Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M)) ≅
          (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.mapComp' (f' i).op.toLoc r₁.op.toLoc
        m.op.toLoc (by rw [← G₁]; rfl))).symm.app ((Scheme.Modules.pullback p).obj M)
    let T₂ :
        (Scheme.Modules.pullback r₂).obj
            ((Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M)) ≅
          (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) :=
      (Cat.Hom.toNatIso (Mdl.mapComp' (f' j).op.toLoc r₂.op.toLoc
        m.op.toLoc (by rw [← G₂]; rfl))).symm.app ((Scheme.Modules.pullback p).obj M)
    N ≫ (C₂ ≪≫ (Scheme.Modules.pullback r₂).mapIso K₂ ≪≫ T₂).hom =
      (C₁ ≪≫ (Scheme.Modules.pullback r₁).mapIso K₁ ≪≫ T₁).hom := by
  intro N C₁ C₂ K₁ K₂ T₁ T₂
  have hN := congrArg
    (fun γ : (Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M) ⟶
        (Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M) =>
      (Scheme.Modules.pullback s).map γ)
    (canonicalTransition_eq_prescribed (f i) (f j) d a₁ a₂ e₁ e₂ M)
  have H := prescribed_pullback_leg_relation
    f f' p p' w M d m s i j a₁ a₂ r₁ r₂ e₁ e₂ G₁ G₂ E₁ E₂ hq
  exact (congrArg
    (fun n : (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ⟶
      (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) =>
      n ≫ (C₂ ≪≫ (Scheme.Modules.pullback r₂).mapIso K₂ ≪≫ T₂).hom) hN).trans H

/-- Canonical overlap coherence in the native module categories.
Every commutative square is supplied by the original geometric maps. -/
theorem canonical_pullback_native_leg_relation
    {ι : Type t} {S S' : Scheme.{u}} {X X' : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) (f' : ∀ i, X' i ⟶ S')
    (p : S' ⟶ S) (p' : ∀ i, X' i ⟶ X i)
    (w : ∀ i, p' i ≫ f i = f' i ≫ p)
    (M : S.Modules)
    {Y V : Scheme.{u}} (d : Y ⟶ S) (m : V ⟶ S') (s : V ⟶ Y)
    (i j : ι) (a₁ : Y ⟶ X i) (a₂ : Y ⟶ X j)
    (r₁ : V ⟶ X' i) (r₂ : V ⟶ X' j)
    (e₁ : a₁ ≫ f i = d) (e₂ : a₂ ≫ f j = d)
    (G₁ : r₁ ≫ f' i = m) (G₂ : r₂ ≫ f' j = m)
    (E₁ : s ≫ a₁ = r₁ ≫ p' i) (E₂ : s ≫ a₂ = r₂ ≫ p' j)
    (hq : s ≫ d = m ≫ p) :
    let N :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ⟶
          (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) :=
      (Scheme.Modules.pullback s).map
        (canonicalTransition (f i) (f j) d a₁ a₂ e₁ e₂ M)
    let C₁ :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ≅
          (Scheme.Modules.pullback r₁).obj
            ((Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M)) :=
      (Scheme.Modules.pullbackComp s a₁ ≪≫ Scheme.Modules.pullbackCongr E₁ ≪≫
        (Scheme.Modules.pullbackComp r₁ (p' i)).symm).app
          ((Scheme.Modules.pullback (f i)).obj M)
    let C₂ :
        (Scheme.Modules.pullback s).obj
            ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) ≅
          (Scheme.Modules.pullback r₂).obj
            ((Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M)) :=
      (Scheme.Modules.pullbackComp s a₂ ≪≫ Scheme.Modules.pullbackCongr E₂ ≪≫
        (Scheme.Modules.pullbackComp r₂ (p' j)).symm).app
          ((Scheme.Modules.pullback (f j)).obj M)
    let K₁ :
        (Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M) ≅
          (Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Scheme.Modules.pullbackComp (p' i) (f i) ≪≫ Scheme.Modules.pullbackCongr (w i) ≪≫
        (Scheme.Modules.pullbackComp (f' i) p).symm).app M
    let K₂ :
        (Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M) ≅
          (Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M) :=
      (Scheme.Modules.pullbackComp (p' j) (f j) ≪≫ Scheme.Modules.pullbackCongr (w j) ≪≫
        (Scheme.Modules.pullbackComp (f' j) p).symm).app M
    let T₁ :
        (Scheme.Modules.pullback r₁).obj
            ((Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M)) ≅
          (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) :=
      (Scheme.Modules.pullbackComp r₁ (f' i) ≪≫ Scheme.Modules.pullbackCongr G₁).app
        ((Scheme.Modules.pullback p).obj M)
    let T₂ :
        (Scheme.Modules.pullback r₂).obj
            ((Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M)) ≅
          (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) :=
      (Scheme.Modules.pullbackComp r₂ (f' j) ≪≫ Scheme.Modules.pullbackCongr G₂).app
        ((Scheme.Modules.pullback p).obj M)
    N ≫ (C₂ ≪≫ (Scheme.Modules.pullback r₂).mapIso K₂ ≪≫ T₂).hom =
      (C₁ ≪≫ (Scheme.Modules.pullback r₁).mapIso K₁ ≪≫ T₁).hom := by
  intro N C₁ C₂ K₁ K₂ T₁ T₂
  have H := canonical_pullback_leg_relation
    f f' p p' w M d m s i j a₁ a₂ r₁ r₂ e₁ e₂ G₁ G₂ E₁ E₂ hq
  have hC₁ := square_component_eq s a₁ r₁ (p' i) E₁
    ((Scheme.Modules.pullback (f i)).obj M)
  have hC₂ := square_component_eq s a₂ r₂ (p' j) E₂
    ((Scheme.Modules.pullback (f j)).obj M)
  have hK₁ := square_component_eq (p' i) (f i) (f' i) p (w i) M
  have hK₂ := square_component_eq (p' j) (f j) (f' j) p (w j) M
  have hT₁ := composition_component_eq r₁ (f' i) m G₁ ((Scheme.Modules.pullback p).obj M)
  have hT₂ := composition_component_eq r₂ (f' j) m G₂ ((Scheme.Modules.pullback p).obj M)
  have hmap₁ := congrArg
    (fun e : (Scheme.Modules.pullback (p' i)).obj ((Scheme.Modules.pullback (f i)).obj M) ≅
        (Scheme.Modules.pullback (f' i)).obj ((Scheme.Modules.pullback p).obj M) =>
      (Scheme.Modules.pullback r₁).mapIso e) hK₁
  have hmap₂ := congrArg
    (fun e : (Scheme.Modules.pullback (p' j)).obj ((Scheme.Modules.pullback (f j)).obj M) ≅
        (Scheme.Modules.pullback (f' j)).obj ((Scheme.Modules.pullback p).obj M) =>
      (Scheme.Modules.pullback r₂).mapIso e) hK₂
  have hIso₁ := congrArg₂ Iso.trans hC₁ (congrArg₂ Iso.trans hmap₁ hT₁)
  have hIso₂ := congrArg₂ Iso.trans hC₂ (congrArg₂ Iso.trans hmap₂ hT₂)
  have hleg₁ := congrArg
    (fun e : (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback a₁).obj ((Scheme.Modules.pullback (f i)).obj M)) ≅
        (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) => e.hom) hIso₁
  have hleg₂ := congrArg
    (fun e : (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) ≅
        (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) => e.hom) hIso₂
  have hsecond := congrArg
    (fun z : (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback a₂).obj ((Scheme.Modules.pullback (f j)).obj M)) ⟶
        (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback p).obj M) => N ≫ z) hleg₂
  exact hsecond.symm.trans (H.trans hleg₁)

end AlgebraicCurves.Geometry.Sheaves.DescentComparison

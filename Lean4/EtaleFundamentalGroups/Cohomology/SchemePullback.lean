/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Classical.AbelianSheafFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Scheme pullback of actual constant-coefficient cohomology

The map is induced on Ext by the exact inverse-image functor of abelian
étale sheaves, with both constant objects identified by the actual
constant-sheaf comparison. Its degree-one value is represented by the
inverse image of the original extension with these identifications.

This constructs geometric pullback independently of the fundamental-group
character comparison. Compatibility with monodromy is not assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u})

/-- Pullback on actual derived cohomology, induced by exact inverse image. -/
def constantCohomologyPullback (n : ℕ) :
    Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) n →+
      Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n where
  toFun a :=
    ((Ext.mk₀ ((etaleAbelianPullbackConstantIso f).app
      (AddCommGrpCat.of (ULift.{u} ℤ))).inv).comp
        (a.mapExactFunctor (etaleAbelianPullback f)) (zero_add n)).comp
      (Ext.mk₀ ((etaleAbelianPullbackConstantIso f).app A).hom) (add_zero n)
  map_zero' := by
    rw [Ext.mapExactFunctor_zero, Ext.comp_zero, Ext.zero_comp]
  map_add' a b := by
    rw [Ext.mapExactFunctor_add, Ext.comp_add, Ext.add_comp]

/-- Exact inverse image commutes with maps of the original constant coefficients. -/
theorem constantCohomologyPullback_naturality
    (B : AddCommGrpCat.{u}) (α : A ⟶ B) (n : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α) n
        (constantCohomologyPullback f A n a) =
      constantCohomologyPullback f B n
        (Sheaf.H.map ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map α) n a) := by
  let F := etaleAbelianPullback f
  let eZ := (etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let eA := (etaleAbelianPullbackConstantIso f).app A
  let eB := (etaleAbelianPullbackConstantIso f).app B
  let cY := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map α
  let cX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α
  have hn : F.map cY ≫ eB.hom = eA.hom ≫ cX :=
    (etaleAbelianPullbackConstantIso f).hom.naturality α
  change (((Ext.mk₀ eZ.inv).comp (a.mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ eA.hom) (add_zero n)).comp (Ext.mk₀ cX) (add_zero n) =
    ((Ext.mk₀ eZ.inv).comp ((a.comp (Ext.mk₀ cY) (add_zero n)).mapExactFunctor F)
      (zero_add n)).comp (Ext.mk₀ eB.hom) (add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  exact congrArg
    (fun k => (Ext.mk₀ eZ.inv).comp
      ((a.mapExactFunctor F).comp (Ext.mk₀ k) (add_zero n)) (zero_add n)) hn.symm

variable {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))
  (h : i ≫ p = 0)

/-- The inverse-image extension with the original constant coefficient objects. -/
def schemePullbackH1Extension :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (((etaleAbelianPullbackConstantIso f).app A).inv ≫
      (etaleAbelianPullback f).map i)
    ((etaleAbelianPullback f).map p ≫
      ((etaleAbelianPullbackConstantIso f).app
        (AddCommGrpCat.of (ULift.{u} ℤ))).hom)
    (by
      rw [Category.assoc, ← Category.assoc ((etaleAbelianPullback f).map i),
        ← Functor.map_comp, h, Functor.map_zero, zero_comp, comp_zero])

private def schemePullbackH1ExtensionIso :
    (ShortComplex.mk i p h).map (etaleAbelianPullback f) ≅
      schemePullbackH1Extension f A i p h :=
  ShortComplex.isoMk
    ((etaleAbelianPullbackConstantIso f).app A)
    (Iso.refl ((etaleAbelianPullback f).obj E))
    ((etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ)))
    (by
      change ((etaleAbelianPullbackConstantIso f).app A).hom ≫
        (((etaleAbelianPullbackConstantIso f).app A).inv ≫
          (etaleAbelianPullback f).map i) =
        (etaleAbelianPullback f).map i ≫ 𝟙 _
      rw [Iso.hom_inv_id_assoc, Category.comp_id])
    (by
      change 𝟙 _ ≫ ((etaleAbelianPullback f).map p ≫ _) =
        (etaleAbelianPullback f).map p ≫ _
      rw [Category.id_comp])

/-- Exactness is supplied by exact inverse image and the constant comparisons. -/
theorem schemePullbackH1Extension_shortExact
    (hs : (ShortComplex.mk i p h).ShortExact) :
    (schemePullbackH1Extension f A i p h).ShortExact :=
  ShortComplex.shortExact_of_iso (schemePullbackH1ExtensionIso f A i p h)
    (hs.map_of_exact (etaleAbelianPullback f))

/-- The geometric inverse-image extension represents the pullback of its
original derived H¹ class. No extension-class compatibility is postulated. -/
theorem constantCohomologyPullback_extClass
    (hs : (ShortComplex.mk i p h).ShortExact) :
    constantCohomologyPullback f A 1 hs.extClass =
      (schemePullbackH1Extension_shortExact f A i p h hs).extClass := by
  let F := etaleAbelianPullback f
  let eA := (etaleAbelianPullbackConstantIso f).app A
  let eZ := (etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let hm := hs.map_of_exact F
  let ht := schemePullbackH1Extension_shortExact f A i p h hs
  have hn := ShortComplex.ShortExact.extClass_naturality hm ht
    (schemePullbackH1ExtensionIso f A i p h).hom
  change hm.extClass.comp (Ext.mk₀ eA.hom) (add_zero 1) =
    (Ext.mk₀ eZ.hom).comp ht.extClass (zero_add 1) at hn
  change ((Ext.mk₀ eZ.inv).comp (hs.extClass.mapExactFunctor F) (zero_add 1)).comp
    (Ext.mk₀ eA.hom) (add_zero 1) = ht.extClass
  rw [Ext.mapExactFunctor_extClass, Ext.comp_assoc_of_third_deg_zero, hn]
  exact (Ext.mk₀_comp_mk₀_assoc eZ.inv eZ.hom ht.extClass).trans (by
    rw [eZ.inv_hom_id]
    exact Ext.mk₀_id_comp ht.extClass)

end EtaleFundamentalGroups.Cohomology

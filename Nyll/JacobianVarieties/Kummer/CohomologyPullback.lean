/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Actual pullback of constant-coefficient etale cohomology

Use the exact inverse image of abelian sheaves and its actual comparison with
constant sheaves. In degree one, the resulting map sends an extension class
to the class of its inverse-image extension, with the original coefficient
and integer sheaves. This construction does not define cohomology by characters.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian EtaleCohomology

universe u

namespace JacobianVarieties.Kummer

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback on actual derived cohomology, retaining constant coefficients. -/
def constantCohomologyPullback (A : AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) n →+
      Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n :=
  let P := etaleAbelianPullback f
  let e := etaleAbelianPullbackConstantIso f
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  ((Ext.mk₀ (e.hom.app A)).postcomp
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z) (add_zero n)).comp
      (((Ext.mk₀ (e.inv.app Z)).precomp
        (P.obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A))
        (zero_add n)).comp
          (P.mapExtAddHom
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj Z)
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) n))

/-- The map uses the actual exact-functor map on `Ext`. -/
theorem constantCohomologyPullback_apply (A : AddCommGrpCat.{u}) (n : ℕ)
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    constantCohomologyPullback f A n a =
      ((Ext.mk₀ ((etaleAbelianPullbackConstantIso f).inv.app
        (AddCommGrpCat.of (ULift.{u} ℤ)))).comp
          (a.mapExactFunctor (etaleAbelianPullback f)) (zero_add n)).comp
            (Ext.mk₀ ((etaleAbelianPullbackConstantIso f).hom.app A)) (add_zero n) := rfl

variable (A : AddCommGrpCat.{u})
  {E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) (h : i ≫ p = 0)

/-- The inverse-image extension, identifying both endpoints with the original
constant sheaves through the actual inverse-image comparison. -/
abbrev pullbackExtension : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  let P := etaleAbelianPullback f
  let e := etaleAbelianPullbackConstantIso f
  ShortComplex.mk (e.inv.app A ≫ P.map i)
    (P.map p ≫ e.hom.app (AddCommGrpCat.of (ULift.{u} ℤ))) (by
      rw [Category.assoc, ← Category.assoc (P.map i), ← P.map_comp, h,
        P.map_zero, Limits.zero_comp, Limits.comp_zero])

private def pullbackExtensionIso :
    pullbackExtension f A i p h ≅ (ShortComplex.mk i p h).map (etaleAbelianPullback f) := by
  let P : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullback f
  let e : constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⋙ P ≅
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleAbelianPullbackConstantIso f
  let Z : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  refine ShortComplex.isoMk (e.app A).symm (Iso.refl (P.obj E)) (e.app Z).symm ?_ ?_
  · change e.inv.app A ≫ P.map i = (e.inv.app A ≫ P.map i) ≫ 𝟙 (P.obj E)
    rw [Category.comp_id]
  · change 𝟙 (P.obj E) ≫ P.map p = (P.map p ≫ e.hom.app Z) ≫ e.inv.app Z
    rw [Category.id_comp, Category.assoc, e.hom_inv_id_app Z]
    exact (Category.comp_id (P.map p)).symm

/-- Exactness is supplied by exact inverse image; no additional exactness
condition is imposed on the pulled-back extension. -/
theorem pullbackExtension_shortExact (hs : (ShortComplex.mk i p h).ShortExact) :
    (pullbackExtension f A i p h).ShortExact :=
  ShortComplex.shortExact_of_iso (pullbackExtensionIso f A i p h).symm
    (hs.map_of_exact (etaleAbelianPullback f))

/-- Pullback of an actual degree-one cohomology class is represented by
the actual inverse-image short exact sequence. -/
theorem constantCohomologyPullback_extClass
    (hs : (ShortComplex.mk i p h).ShortExact) :
    constantCohomologyPullback f A 1 hs.extClass =
      (pullbackExtension_shortExact f A i p h hs).extClass := by
  let P := etaleAbelianPullback f
  let e := etaleAbelianPullbackConstantIso f
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  have hs' := pullbackExtension_shortExact f A i p h hs
  have hn := ShortComplex.ShortExact.extClass_naturality hs'
    (hs.map_of_exact P) (pullbackExtensionIso f A i p h).hom
  change hs'.extClass.comp (Ext.mk₀ (e.inv.app A)) (add_zero 1) =
    (Ext.mk₀ (e.inv.app Z)).comp (hs.map_of_exact P).extClass (zero_add 1) at hn
  rw [constantCohomologyPullback_apply, Ext.mapExactFunctor_extClass, ← hn,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    e.inv_hom_id_app A, Ext.comp_mk₀_id]

end JacobianVarieties.Kummer

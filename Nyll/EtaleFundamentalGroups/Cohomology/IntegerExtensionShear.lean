/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSquare
import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation
import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Constant torsor translations as additive shears

On the fiber of an extension over the integer section one, translation by a
coefficient is the restriction of the additive endomorphism e ↦ e + i(a p(e)).
This realizes the torsor action using genuine abelian-sheaf morphisms, so its
compatibility with inverse image follows from additivity and the naturality
of the existing constant-coefficient comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- The constant-sheaf map sending one to the specified original coefficient. -/
def constantIntegerMultiple (X : Scheme.{u}) (A : AddCommGrpCat.{u}) (a : A) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
    (AddCommGrpCat.ofHom (uliftZMultiplesHom A a))

/-- This map sends the actual integer-one section to the original coefficient section. -/
theorem constantIntegerMultiple_one (X : Scheme.{u}) (A : AddCommGrpCat.{u}) (a : A)
    (U : X.Etaleᵒᵖ) :
    (constantIntegerMultiple X A a).hom.app U ((integerUnitSection X).app U PUnit.unit) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U a := by
  let k := AddCommGrpCat.ofHom (uliftZMultiplesHom A a)
  have hnNat := toSheafify_naturality X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).map k)
  have hnU := congrArg
    (fun η : (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A) => η.app U) hnNat
  have hn := ConcreteCategory.congr_hom hnU (ULift.up 1)
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U
      (uliftZMultiplesHom A a (ULift.up 1)) =
    (constantIntegerMultiple X A a).hom.app U ((integerUnitSection X).app U PUnit.unit) at hn
  have ha : uliftZMultiplesHom A a (ULift.up 1) = a := by
    rw [uliftZMultiplesHom_apply_apply]
    exact one_zsmul a
  rw [ha] at hn
  exact hn.symm

variable {X : Scheme.{u}} (A : AddCommGrpCat.{u})
  {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- An additive middle-sheaf endomorphism realizing coefficient translation
on the fiber over one. -/
def integerExtensionShear (a : A) : E ⟶ E :=
  (p ≫ constantIntegerMultiple X A a) ≫ i + 𝟙 E

/-- The original translation on the actual lift sheaf is the restriction of this additive shear. -/
theorem constantFiberTranslation_inclusion_eq_shear (h : i ≫ p = 0) (a : A) :
    constantFiberTranslation A i p h (integerUnitSection X) a ≫
        extensionFiberInclusion (ShortComplex.mk i p h) (integerUnitSection X) =
      extensionFiberInclusion (ShortComplex.mk i p h) (integerUnitSection X) ≫
        (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
          (integerExtensionShear A i p a) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro (e : {b : E.obj.obj U // p.hom.app U b =
    (integerUnitSection X).app U PUnit.unit})
  change i.hom.app U
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U a) + e.val =
    i.hom.app U ((constantIntegerMultiple X A a).hom.app U (p.hom.app U e.val)) + e.val
  rw [e.property, constantIntegerMultiple_one]

variable {Y : Scheme.{u}} (f : Y ⟶ X)

/-- The additive shear commutes with actual abelian inverse image and the original
coefficient identifications. -/
theorem integerExtensionShear_pullback (h : i ≫ p = 0) (a : A) :
    (etaleAbelianPullback f).map (integerExtensionShear A i p a) =
      integerExtensionShear A (schemePullbackH1Extension f A i p h).f
        (schemePullbackH1Extension f A i p h).g a := by
  let F := etaleAbelianPullback f
  let eA := (etaleAbelianPullbackConstantIso f).app A
  let eZ := (etaleAbelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))
  have hn := (etaleAbelianPullbackConstantIso f).hom.naturality
    (AddCommGrpCat.ofHom (uliftZMultiplesHom A a))
  change F.map (constantIntegerMultiple X A a) ≫ eA.hom =
    eZ.hom ≫ constantIntegerMultiple Y A a at hn
  have hn' : F.map (constantIntegerMultiple X A a) =
      eZ.hom ≫ constantIntegerMultiple Y A a ≫ eA.inv := by
    calc
      F.map (constantIntegerMultiple X A a) =
          (F.map (constantIntegerMultiple X A a) ≫ eA.hom) ≫ eA.inv := by
        rw [Category.assoc, eA.hom_inv_id]
        exact (Category.comp_id (F.map (constantIntegerMultiple X A a))).symm
      _ = (eZ.hom ≫ constantIntegerMultiple Y A a) ≫ eA.inv :=
        congrArg (fun k => k ≫ eA.inv) hn
      _ = eZ.hom ≫ constantIntegerMultiple Y A a ≫ eA.inv := Category.assoc _ _ _
  change F.map ((p ≫ constantIntegerMultiple X A a) ≫ i + 𝟙 E) =
    (((F.map p ≫ eZ.hom) ≫ constantIntegerMultiple Y A a) ≫
      (eA.inv ≫ F.map i)) + 𝟙 (F.obj E)
  rw [F.map_add, F.map_comp, F.map_comp, F.map_id E, hn']
  simp only [Category.assoc]

end EtaleFundamentalGroups.Cohomology

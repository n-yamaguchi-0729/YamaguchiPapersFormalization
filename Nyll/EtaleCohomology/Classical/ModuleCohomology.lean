/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Coefficient modules on classical sheaf cohomology

The underlying additive groups are mathlib's `CategoryTheory.Sheaf.H`.
Scalar multiplication is induced by multiplication on the coefficient sheaf.
The module structures are bundled in `ModuleCat`, avoiding competing global
module instances on the underlying Ext groups.
-/


noncomputable section

universe u v w t h

open CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology.Classical

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type t} [Ring R]
variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- Forget the coefficient action, retaining the underlying classical abelian sheaf. -/
abbrev forgetCoefficients :
    Sheaf J (ModuleCat.{w} R) ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})

/-- Multiplication by a coefficient, as an endomorphism of the underlying abelian sheaf. -/
def coefficientAction (F : Sheaf J (ModuleCat.{w} R)) (r : R) :
    (forgetCoefficients.obj F) ⟶ (forgetCoefficients.obj F) :=
  ObjectProperty.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun x => r • x
          map_zero' := smul_zero r
          map_add' := smul_add r }
      naturality := fun U V f => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        exact ((F.obj.map f).hom.map_smul r x).symm }

lemma coefficientAction_one (F : Sheaf J (ModuleCat.{w} R)) :
    coefficientAction F 1 = 𝟙 (forgetCoefficients.obj F) := by
  ext U x
  change F.obj.obj U at x
  change (1 : R) • (x : F.obj.obj U) = x
  exact one_smul R x

lemma coefficientAction_zero (F : Sheaf J (ModuleCat.{w} R)) :
    coefficientAction F 0 = 0 := by
  ext U x
  change F.obj.obj U at x
  change (0 : R) • (x : F.obj.obj U) = 0
  exact zero_smul R x

lemma coefficientAction_add (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    coefficientAction F (r + s) = coefficientAction F r + coefficientAction F s := by
  ext U x
  change F.obj.obj U at x
  change (r + s) • (x : F.obj.obj U) = r • x + s • x
  exact add_smul r s x

lemma coefficientAction_mul (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    coefficientAction F (r * s) = coefficientAction F s ≫ coefficientAction F r := by
  ext U x
  change F.obj.obj U at x
  change (r * s) • (x : F.obj.obj U) = r • (s • x)
  exact mul_smul r s x

lemma coefficientAction_naturality {F G : Sheaf J (ModuleCat.{w} R)}
    (f : F ⟶ G) (r : R) :
    coefficientAction F r ≫ forgetCoefficients.map f =
      forgetCoefficients.map f ≫ coefficientAction G r := by
  ext U x
  exact (f.hom.app U).hom.map_smul r x

variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{h} (Sheaf J AddCommGrpCat.{w})]

/-- The coefficient action on the existing Ext definition of classical cohomology. -/
abbrev cohomologyModule (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    Module R ((forgetCoefficients.obj F).H n) where
  smul r x := Sheaf.H.map (coefficientAction F r) n x
  one_smul x := by
    change Sheaf.H.map (coefficientAction F 1) n x = x
    rw [coefficientAction_one, Sheaf.H.map_id_apply]
  mul_smul r s x := by
    change Sheaf.H.map (coefficientAction F (r * s)) n x =
      Sheaf.H.map (coefficientAction F r) n (Sheaf.H.map (coefficientAction F s) n x)
    rw [coefficientAction_mul, Sheaf.H.map_comp_apply]
  smul_zero r := (Sheaf.H.map (coefficientAction F r) n).map_zero
  smul_add r x y := (Sheaf.H.map (coefficientAction F r) n).map_add x y
  add_smul r s x := by
    change Sheaf.H.map (coefficientAction F (r + s)) n x =
      Sheaf.H.map (coefficientAction F r) n x + Sheaf.H.map (coefficientAction F s) n x
    rw [coefficientAction_add, Sheaf.H.map_add_apply]
  zero_smul x := by
    change Sheaf.H.map (coefficientAction F 0) n x = 0
    rw [coefficientAction_zero]
    change (Sheaf.functorH J n).map 0 x = 0
    rw [Functor.map_zero]
    rfl

/-- Classical sheaf cohomology with its canonical coefficient module structure. -/
def cohomology (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) : ModuleCat.{h} R :=
  letI := cohomologyModule F n
  ModuleCat.of R ((forgetCoefficients.obj F).H n)

/-- Scalar multiplication is the cohomology map of the scalar endomorphism of the sheaf. -/
lemma cohomology_smul (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) (r : R)
    (x : cohomology F n) :
    r • x = Sheaf.H.map (coefficientAction F r) n x := rfl

/-- A morphism of coefficient sheaves induces a linear map on classical cohomology. -/
def cohomologyMap {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) (n : ℕ) :
    cohomology F n →ₗ[R] cohomology G n where
  toFun := Sheaf.H.map (forgetCoefficients.map f) n
  map_add' := (Sheaf.H.map (forgetCoefficients.map f) n).map_add
  map_smul' r x := by
    change (forgetCoefficients.obj F).H n at x
    change Sheaf.H.map (forgetCoefficients.map f) n
        (Sheaf.H.map (coefficientAction F r) n x) =
      Sheaf.H.map (coefficientAction G r) n
        (Sheaf.H.map (forgetCoefficients.map f) n x)
    rw [← Sheaf.H.map_comp_apply, coefficientAction_naturality,
      Sheaf.H.map_comp_apply]

/-- The underlying function of the coefficient-linear map is the classical cohomology map. -/
lemma cohomologyMap_apply {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) (n : ℕ)
    (x : cohomology F n) :
    cohomologyMap f n x = Sheaf.H.map (forgetCoefficients.map f) n x := rfl

/-- The usual degree-zero comparison is linear over the coefficient ring. -/
def cohomologyZeroEquiv (F : Sheaf J (ModuleCat.{w} R))
    {T : C} (hT : IsTerminal T) :
    cohomology F 0 ≃ₗ[R] F.obj.obj (op T) where
  toAddEquiv := Sheaf.H.equiv₀ (forgetCoefficients.obj F) hT
  map_smul' r x :=
    (Sheaf.H.equiv₀_naturality hT (coefficientAction F r) x).symm

/-- Naturality of the coefficient-linear degree-zero comparison. -/
lemma cohomologyZeroEquiv_naturality {F G : Sheaf J (ModuleCat.{w} R)}
    (f : F ⟶ G) {T : C} (hT : IsTerminal T) (x : cohomology F 0) :
    cohomologyZeroEquiv G hT (cohomologyMap f 0 x) =
      f.hom.app (op T) (cohomologyZeroEquiv F hT x) :=
  (Sheaf.H.equiv₀_naturality hT (forgetCoefficients.map f) x).symm

end EtaleCohomology.Classical

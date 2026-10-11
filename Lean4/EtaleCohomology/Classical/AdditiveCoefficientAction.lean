/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.End

/-!
# Coefficient actions transported by an additive functor

Scalar endomorphisms of the coefficient group induce scalar endomorphisms of
its image. This constructs the module structure and proves linearity of the
induced maps, without changing the underlying additive groups.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace EtaleCohomology.Classical

variable (F : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{v}) [F.Additive]
  (R : Type w) [Semiring R] (A : AddCommGrpCat.{u}) [Module R A]

private def scalarEnd (r : R) : A ⟶ A :=
  AddCommGrpCat.ofHom (smulAddHom R A r)

private theorem scalarEnd_one : scalarEnd R A 1 = 𝟙 A := by
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (one_smul R)

private theorem scalarEnd_mul (r s : R) :
    scalarEnd R A (r * s) = scalarEnd R A s ≫ scalarEnd R A r := by
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (mul_smul r s)

private theorem scalarEnd_add (r s : R) :
    scalarEnd R A (r + s) = scalarEnd R A r + scalarEnd R A s := by
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (add_smul r s)

private theorem scalarEnd_zero : scalarEnd R A 0 = 0 := by
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (zero_smul R)

/-- The module action obtained by applying an additive functor to the actual
scalar endomorphisms of its coefficient group. -/
abbrev additiveCoefficientModule : Module R (F.obj A) where
  smul r x := F.map (scalarEnd R A r) x
  one_smul x := by
    change F.map (scalarEnd R A 1) x = x
    rw [scalarEnd_one, F.map_id]
    rfl
  mul_smul r s x := by
    change F.map (scalarEnd R A (r * s)) x =
      F.map (scalarEnd R A r) (F.map (scalarEnd R A s) x)
    rw [scalarEnd_mul, F.map_comp]
    rfl
  smul_zero r := (F.map (scalarEnd R A r)).hom.map_zero
  smul_add r x y := (F.map (scalarEnd R A r)).hom.map_add x y
  add_smul r s x := by
    change F.map (scalarEnd R A (r + s)) x =
      F.map (scalarEnd R A r) x + F.map (scalarEnd R A s) x
    rw [scalarEnd_add, F.map_add]
    rfl
  zero_smul x := by
    change F.map (scalarEnd R A 0) x = 0
    rw [scalarEnd_zero, F.map_zero]
    rfl

/-- A coefficient-linear map remains linear under the induced coefficient actions. -/
theorem additiveCoefficient_map_smul (B : AddCommGrpCat.{u}) [Module R B]
    (f : A ⟶ B) (hf : ∀ (r : R) (x : A), f (r • x) = r • f x)
    (r : R) (x : F.obj A) :
    let : Module R (F.obj A) := additiveCoefficientModule F R A
    let : Module R (F.obj B) := additiveCoefficientModule F R B
    F.map f (r • x) = r • F.map f x := by
  change F.map f (F.map (scalarEnd R A r) x) =
    F.map (scalarEnd R B r) (F.map f x)
  have h : scalarEnd R A r ≫ f = f ≫ scalarEnd R B r := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext (hf r)
  exact (congrArg (fun k => k x) (F.map_comp (scalarEnd R A r) f)).symm.trans
    ((congrArg (fun k => F.map k x) h).trans
      (congrArg (fun k => k x) (F.map_comp f (scalarEnd R B r))))

end EtaleCohomology.Classical

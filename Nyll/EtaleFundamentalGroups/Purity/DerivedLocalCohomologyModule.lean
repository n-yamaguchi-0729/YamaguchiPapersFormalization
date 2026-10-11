/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalar
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The module of derived local-cohomology classes

The scalar endomorphisms of the additive-group colimit satisfy the module
laws.  We package this action in an object of `ModuleCat R`, retaining the
original additive group.  The module structure is installed only while
constructing that object; no additional global instance is put on the
underlying additive-group colimit.

The colimit maps out of the derived-Ext groups are linear.  Every class in
the resulting module is annihilated by a power of the support ideal.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- Scalar endomorphisms of derived local cohomology respect addition. -/
theorem derivedLocalCohomologyScalarMap_add
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (a b : R) :
    derivedLocalCohomologyScalarMap I M i (a + b) =
      derivedLocalCohomologyScalarMap I M i a +
        derivedLocalCohomologyScalarMap I M i b := by
  apply colimit.hom_ext (F := derivedLocalCohomologyPowersDiagram I M i)
  rintro ⟨⟨n⟩⟩
  ext α
  let ι : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i →+ derivedLocalCohomology I M i :=
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n))).hom
  change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i at α
  change
    derivedLocalCohomologyScalarMap I M i (a + b)
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) α) =
      derivedLocalCohomologyScalarMap I M i a
          (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
            (op (op n)) α) +
        derivedLocalCohomologyScalarMap I M i b
          (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
            (op (op n)) α)
  exact (derivedLocalCohomologyScalarMap_ι_apply I M i (a + b) n α).trans
    ((congrArg ι
      (add_smul a b α)).trans
        ((map_add ι
          (a • α) (b • α)).trans
            (congrArg₂ (fun x y : derivedLocalCohomology I M i => x + y)
              (derivedLocalCohomologyScalarMap_ι_apply I M i a n α).symm
              (derivedLocalCohomologyScalarMap_ι_apply I M i b n α).symm)))

/-- The zero scalar induces the zero endomorphism. -/
theorem derivedLocalCohomologyScalarMap_zero
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomologyScalarMap I M i 0 = 0 := by
  apply colimit.hom_ext (F := derivedLocalCohomologyPowersDiagram I M i)
  rintro ⟨⟨n⟩⟩
  ext α
  let ι : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i →+ derivedLocalCohomology I M i :=
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n))).hom
  change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M i at α
  change
    derivedLocalCohomologyScalarMap I M i 0
      (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
        (op (op n)) α) = 0
  exact (derivedLocalCohomologyScalarMap_ι_apply I M i 0 n α).trans
    ((congrArg ι
      (zero_smul R α)).trans
        (map_zero ι))

/-- The scalar endomorphisms furnish the module laws on the existing
additive group.  This definition is deliberately not an instance. -/
@[instance_reducible] private def derivedLocalCohomologyModuleStructure
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    Module R (derivedLocalCohomology I M i) where
  smul a z := derivedLocalCohomologyScalarMap I M i a z
  one_smul z :=
    ConcreteCategory.congr_hom (derivedLocalCohomologyScalarMap_one I M i) z
  mul_smul a b z :=
    ConcreteCategory.congr_hom (derivedLocalCohomologyScalarMap_mul I M i a b) z
  smul_zero a := map_zero (ConcreteCategory.hom
    (derivedLocalCohomologyScalarMap I M i a))
  smul_add a z w := map_add (ConcreteCategory.hom
    (derivedLocalCohomologyScalarMap I M i a)) z w
  add_smul a b z :=
    ConcreteCategory.congr_hom (derivedLocalCohomologyScalarMap_add I M i a b) z
  zero_smul z :=
    ConcreteCategory.congr_hom (derivedLocalCohomologyScalarMap_zero I M i) z

/-- Derived local cohomology as an `R`-module, with the additive group of
its original derived-Ext colimit. -/
def derivedLocalCohomologyModule
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R := by
  letI : Module R (derivedLocalCohomology I M i) :=
    derivedLocalCohomologyModuleStructure I M i
  exact ModuleCat.of R (derivedLocalCohomology I M i)

/-- Forgetting the module action recovers the original additive-group
colimit, including its existing additive-group structure. -/
theorem derivedLocalCohomologyModule_forget
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (derivedLocalCohomologyModule I M i) =
      derivedLocalCohomology I M i :=
  rfl

/-- Scalar multiplication in the bundled module is the previously
constructed colimit endomorphism. -/
theorem derivedLocalCohomologyModule_smul
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (a : R)
    (z : derivedLocalCohomologyModule I M i) :
    a • z = derivedLocalCohomologyScalarMap I M i a z :=
  rfl

/-- The colimit injection from the `n`-th derived-Ext group is linear. -/
def derivedLocalCohomologyModuleι
    (I : Ideal R) (M : ModuleCat.{u} R) (i n : ℕ) :
    CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ n)) M i →ₗ[R]
        derivedLocalCohomologyModule I M i where
  toFun := ConcreteCategory.hom
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M i) (op (op n)))
  map_add' α β :=
    map_add (ConcreteCategory.hom
      (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
        (op (op n)))) α β
  map_smul' a α := by
    change
      colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
          (op (op n)) (a • α) =
        derivedLocalCohomologyScalarMap I M i a
          (colimit.ι (derivedLocalCohomologyPowersDiagram I M i)
            (op (op n)) α)
    exact (derivedLocalCohomologyScalarMap_ι_apply I M i a n α).symm

/-- Every class in the local-cohomology module is annihilated by every
member of some power of the support ideal. -/
theorem derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (z : derivedLocalCohomologyModule I M i) :
    ∃ n : ℕ, ∀ a : R, a ∈ I ^ n → a • z = 0 :=
  derivedLocalCohomology_exists_idealPower_scalarMap_eq_zero I M i z

end EtaleFundamentalGroups

end

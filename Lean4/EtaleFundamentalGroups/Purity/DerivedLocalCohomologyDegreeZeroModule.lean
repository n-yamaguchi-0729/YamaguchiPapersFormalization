/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalar
import EtaleFundamentalGroups.Purity.ResidueFieldHullSocle
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Degree-zero local cohomology inside the coefficient module

In degree zero, a representative is a map from a quotient ring to the
coefficient module.  Evaluation at one is compatible with the quotient
transition maps and hence defines a linear map out of local cohomology.
Each representative evaluation is injective, so the colimit map is
injective.  If every coefficient vector is killed by a power of the
support ideal, the map is also surjective.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

private def derivedExtZeroQuotientTorsionEquiv (J : Ideal R) (M : ModuleCat.{u} R) :
    CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ J)) M 0 ≃ₗ[R]
      Submodule.torsionBySet R M J :=
  (CategoryTheory.Abelian.Ext.linearEquiv₀.trans
    (ModuleCat.homLinearEquiv (R := R) (S := R))).trans
      (Purity.quotientHomEquivTorsionBySet J)

private def derivedExtZeroQuotientEvaluation (J : Ideal R) (M : ModuleCat.{u} R) :
    CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ J)) M 0 →ₗ[R] M :=
  (Submodule.torsionBySet R M J).subtype.comp
    (derivedExtZeroQuotientTorsionEquiv J M).toLinearMap

private theorem derivedExtZeroQuotientEvaluation_mk₀
    (J : Ideal R) (M : ModuleCat.{u} R)
    (f : ModuleCat.of R (R ⧸ J) ⟶ M) :
    derivedExtZeroQuotientEvaluation J M (CategoryTheory.Abelian.Ext.mk₀ f) =
      f.hom (Ideal.Quotient.mk J 1) := by
  change (CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R)
    (CategoryTheory.Abelian.Ext.mk₀ f)).hom (Ideal.Quotient.mk J 1) = _
  have h : CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R)
      (CategoryTheory.Abelian.Ext.mk₀ f) = f :=
    (CategoryTheory.Abelian.Ext.mk₀_bijective _ _).injective
      (CategoryTheory.Abelian.Ext.mk₀_linearEquiv₀_apply _)
  rw [h]

private theorem derivedExtZeroQuotientEvaluation_injective
    (J : Ideal R) (M : ModuleCat.{u} R) :
    Function.Injective (derivedExtZeroQuotientEvaluation J M) :=
  (Submodule.torsionBySet R M (J : Set R)).subtype_injective.comp
    (derivedExtZeroQuotientTorsionEquiv J M).injective

private theorem derivedExtZeroQuotientEvaluation_exists_preimage
    (J : Ideal R) (M : ModuleCat.{u} R) (z : M)
    (hz : z ∈ Submodule.torsionBySet R M (J : Set R)) :
    ∃ α : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ J)) M 0,
      derivedExtZeroQuotientEvaluation J M α = z := by
  let zJ : Submodule.torsionBySet R M (J : Set R) := ⟨z, hz⟩
  refine ⟨(derivedExtZeroQuotientTorsionEquiv J M).symm zJ, ?_⟩
  exact congrArg Subtype.val
    ((derivedExtZeroQuotientTorsionEquiv J M).apply_symm_apply zJ)

private def derivedLocalCohomologyZeroEvaluationCocone
    (I : Ideal R) (M : ModuleCat.{u} R) :
    Cocone (derivedLocalCohomologyPowersDiagram I M 0) where
  pt := AddCommGrpCat.of M
  ι :=
    { app := fun n => AddCommGrpCat.ofHom
        (derivedExtZeroQuotientEvaluation (I ^ unop (unop n)) M).toAddMonoidHom
      naturality := by
        intro j k g
        ext α
        let q : ModuleCat.of R (R ⧸ I ^ unop (unop k)) ⟶
            ModuleCat.of R (R ⧸ I ^ unop (unop j)) :=
          (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)).map g.unop
        change derivedExtZeroQuotientEvaluation (I ^ unop (unop k)) M
            ((CategoryTheory.Abelian.Ext.mk₀ q).comp α (zero_add 0)) =
          derivedExtZeroQuotientEvaluation (I ^ unop (unop j)) M α
        obtain ⟨f, rfl⟩ := (CategoryTheory.Abelian.Ext.mk₀_bijective _ _).surjective α
        let f' : ModuleCat.of R (R ⧸ I ^ unop (unop j)) ⟶ M := f
        change derivedExtZeroQuotientEvaluation (I ^ unop (unop k)) M
            ((CategoryTheory.Abelian.Ext.mk₀ q).comp
              (CategoryTheory.Abelian.Ext.mk₀ f') (zero_add 0)) =
          derivedExtZeroQuotientEvaluation (I ^ unop (unop j)) M
            (CategoryTheory.Abelian.Ext.mk₀ f')
        rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
          derivedExtZeroQuotientEvaluation_mk₀, derivedExtZeroQuotientEvaluation_mk₀]
        change f'.hom (q.hom (Ideal.Quotient.mk (I ^ unop (unop k)) (1 : R))) =
          f'.hom (Ideal.Quotient.mk (I ^ unop (unop j)) (1 : R))
        congr 1 }

private def derivedLocalCohomologyZeroEvaluation
    (I : Ideal R) (M : ModuleCat.{u} R) :
    derivedLocalCohomology I M 0 ⟶ AddCommGrpCat.of M :=
  colimit.desc (derivedLocalCohomologyPowersDiagram I M 0)
    (derivedLocalCohomologyZeroEvaluationCocone I M)

private theorem derivedLocalCohomologyZeroEvaluation_ι
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M 0) :
    derivedLocalCohomologyZeroEvaluation I M
        (colimit.ι (derivedLocalCohomologyPowersDiagram I M 0) (op (op n)) α) =
      derivedExtZeroQuotientEvaluation (I ^ n) M α :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (derivedLocalCohomologyZeroEvaluationCocone I M) (op (op n))) α

/-- Degree-zero local cohomology maps linearly to its coefficient module
by evaluation of quotient homomorphisms at one. -/
def derivedLocalCohomologyZeroToModule (I : Ideal R) (M : ModuleCat.{u} R) :
    derivedLocalCohomologyModule I M 0 →ₗ[R] M where
  toFun := ConcreteCategory.hom (derivedLocalCohomologyZeroEvaluation I M)
  map_add' := map_add (ConcreteCategory.hom
    (derivedLocalCohomologyZeroEvaluation I M))
  map_smul' a z := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
      preservesSmallestFilteredColimits_of_preservesFilteredColimits _
    obtain ⟨k, α, hα⟩ :=
      Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I M 0) z
    rcases k with ⟨⟨n⟩⟩
    change derivedLocalCohomologyZeroEvaluation I M
      (derivedLocalCohomologyScalarMap I M 0 a z) =
        a • derivedLocalCohomologyZeroEvaluation I M z
    rw [← hα]
    change CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M 0 at α
    exact (congrArg (derivedLocalCohomologyZeroEvaluation I M)
      (derivedLocalCohomologyScalarMap_ι_apply I M 0 a n α)).trans
        ((derivedLocalCohomologyZeroEvaluation_ι I M n (a • α)).trans
          ((map_smul (derivedExtZeroQuotientEvaluation (I ^ n) M) a α).trans
            (congrArg (fun z : M => a • z)
              (derivedLocalCohomologyZeroEvaluation_ι I M n α).symm)))

private theorem derivedLocalCohomologyZeroToModule_ι
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (α : CategoryTheory.Abelian.Ext.{u} (ModuleCat.of R (R ⧸ I ^ n)) M 0) :
    derivedLocalCohomologyZeroToModule I M (derivedLocalCohomologyModuleι I M 0 n α) =
      derivedExtZeroQuotientEvaluation (I ^ n) M α :=
  derivedLocalCohomologyZeroEvaluation_ι I M n α

/-- Evaluation of a degree-zero representative given by a quotient
homomorphism is its value at one. -/
theorem derivedLocalCohomologyZeroToModule_ι_mk₀
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (f : ModuleCat.of R (R ⧸ I ^ n) ⟶ M) :
    derivedLocalCohomologyZeroToModule I M
        (derivedLocalCohomologyModuleι I M 0 n (CategoryTheory.Abelian.Ext.mk₀ f)) =
      f.hom (Ideal.Quotient.mk (I ^ n) 1) :=
  (derivedLocalCohomologyZeroToModule_ι I M n (CategoryTheory.Abelian.Ext.mk₀ f)).trans
    (derivedExtZeroQuotientEvaluation_mk₀ (I ^ n) M f)

private theorem eq_zero_of_map_eq_of_eq_zero
    {A B : AddCommGrpCat.{u}} (f : A ⟶ B) {x : A} {y : B}
    (hx : x = 0) (hy : f x = y) : y = 0 := by
  calc
    y = f x := hy.symm
    _ = f 0 := congrArg (ConcreteCategory.hom f) hx
    _ = 0 := map_zero _

/-- No degree-zero class is lost on evaluation in the coefficient module. -/
theorem derivedLocalCohomologyZeroToModule_injective (I : Ideal R) (M : ModuleCat.{u} R) :
    Function.Injective (derivedLocalCohomologyZeroToModule I M) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨k, α, hα⟩ :=
    Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I M 0) z
  rcases k with ⟨⟨n⟩⟩
  have hrep : derivedExtZeroQuotientEvaluation (I ^ n) M α = 0 := by
    exact (derivedLocalCohomologyZeroToModule_ι I M n α).symm.trans
      ((congrArg (derivedLocalCohomologyZeroToModule I M) hα).trans hz)
  have hzero : α = 0 :=
    derivedExtZeroQuotientEvaluation_injective (I ^ n) M
      (hrep.trans (map_zero _).symm)
  exact eq_zero_of_map_eq_of_eq_zero
    (colimit.ι (derivedLocalCohomologyPowersDiagram I M 0) (op (op n))) hzero hα

/-- Every ideal-power torsion vector is represented by a degree-zero
local-cohomology class. -/
theorem derivedLocalCohomologyZeroToModule_exists_preimage
    (I : Ideal R) (M : ModuleCat.{u} R) (z : M)
    (hz : ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    ∃ α : derivedLocalCohomologyModule I M 0,
      derivedLocalCohomologyZeroToModule I M α = z := by
  obtain ⟨n, hn⟩ := hz
  have hzmem : z ∈ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) :=
    (Submodule.mem_torsionBySet_iff (R := R) (M := M)
      (s := ((I ^ n : Ideal R) : Set R)) z).mpr (fun a => hn a a.property)
  obtain ⟨α, hα⟩ :=
    derivedExtZeroQuotientEvaluation_exists_preimage (I ^ n) M z hzmem
  exact ⟨derivedLocalCohomologyModuleι I M 0 n α,
    (derivedLocalCohomologyZeroToModule_ι I M n α).trans hα⟩

/-- The image of degree-zero evaluation consists exactly of the
ideal-power torsion vectors. -/
theorem mem_range_derivedLocalCohomologyZeroToModule_iff
    (I : Ideal R) (M : ModuleCat.{u} R) (z : M) :
    z ∈ LinearMap.range (derivedLocalCohomologyZeroToModule I M) ↔
      ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0 := by
  constructor
  · rintro ⟨α, rfl⟩
    obtain ⟨n, hn⟩ :=
      derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero I M 0 α
    refine ⟨n, ?_⟩
    intro a ha
    rw [← map_smul, hn a ha, map_zero]
  · exact derivedLocalCohomologyZeroToModule_exists_preimage I M z

/-- On an ideal-power torsion module, degree-zero local cohomology is
the entire coefficient module. -/
theorem derivedLocalCohomologyZeroToModule_bijective_of_power_torsion
    (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : ∀ z : M, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    Function.Bijective (derivedLocalCohomologyZeroToModule I M) :=
  ⟨derivedLocalCohomologyZeroToModule_injective I M,
    fun z => derivedLocalCohomologyZeroToModule_exists_preimage I M z (hM z)⟩

end EtaleFundamentalGroups

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientsExact
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Degree-zero coefficient maps on power-torsion modules

Evaluation of degree-zero local cohomology commutes with the second
coefficient map.  When the middle coefficient module is ideal-power
torsion, its evaluation map is surjective.  Exactness of the coefficient
sequence and injectivity of evaluation on the last module then imply
surjectivity of the degree-zero local-cohomology coefficient map.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- Degree-zero evaluation commutes with the second coefficient map. -/
theorem derivedLocalCohomologyZeroToModule_comp_secondMap
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (derivedLocalCohomologyZeroToModule I S.X₃).comp
        (derivedLocalCohomologyModuleCoefficientsSecondMap I hS 0) =
      S.g.hom.comp (derivedLocalCohomologyZeroToModule I S.X₂) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  ext z
  obtain ⟨k, α, hα⟩ :=
    Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I S.X₂ 0) z
  rcases k with ⟨⟨n⟩⟩
  obtain ⟨f, rfl⟩ := (CategoryTheory.Abelian.Ext.mk₀_bijective _ _).surjective α
  change (ModuleCat.of R (R ⧸ I ^ n) ⟶ S.X₂) at f
  change derivedLocalCohomologyZeroToModule I S.X₃
      (derivedLocalCohomologyCoefficientsSecondMap I hS 0 z) =
    S.g.hom (derivedLocalCohomologyZeroToModule I S.X₂ z)
  rw [← hα]
  have hsecond := congrArg (derivedLocalCohomologyZeroToModule I S.X₃)
    (derivedLocalCohomologyCoefficientsSecondMap_ι_apply I hS 0 n
      (CategoryTheory.Abelian.Ext.mk₀ f))
  refine hsecond.trans ?_
  change derivedLocalCohomologyZeroToModule I S.X₃
      (derivedLocalCohomologyModuleι I S.X₃ 0 n
        ((CategoryTheory.Abelian.Ext.mk₀ f).comp
          (CategoryTheory.Abelian.Ext.mk₀ S.g) (add_zero 0))) =
    S.g.hom (derivedLocalCohomologyZeroToModule I S.X₂
      (derivedLocalCohomologyModuleι I S.X₂ 0 n (CategoryTheory.Abelian.Ext.mk₀ f)))
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
    derivedLocalCohomologyZeroToModule_ι_mk₀, derivedLocalCohomologyZeroToModule_ι_mk₀]
  rfl

/-- A surjective coefficient map with ideal-power torsion source induces
a surjection in degree-zero local cohomology. -/
theorem derivedLocalCohomologyModuleCoefficientsSecondMap_surjective_zero_of_power_torsion
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (hT : ∀ z : S.X₂, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    Function.Surjective (derivedLocalCohomologyModuleCoefficientsSecondMap I hS 0) := by
  intro z
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
    (derivedLocalCohomologyZeroToModule I S.X₃ z)
  obtain ⟨y, hy⟩ :=
    (derivedLocalCohomologyZeroToModule_bijective_of_power_torsion I S.X₂ hT).surjective b
  refine ⟨y, (derivedLocalCohomologyZeroToModule_injective I S.X₃) ?_⟩
  calc
    derivedLocalCohomologyZeroToModule I S.X₃
        (derivedLocalCohomologyModuleCoefficientsSecondMap I hS 0 y) =
      S.g.hom (derivedLocalCohomologyZeroToModule I S.X₂ y) :=
        DFunLike.congr_fun (derivedLocalCohomologyZeroToModule_comp_secondMap I hS) y
    _ = derivedLocalCohomologyZeroToModule I S.X₃ z := by rw [hy, hb]

/-- The same degree-zero surjection expressed in the additive-group
category used by the coefficient long exact sequence. -/
theorem derivedLocalCohomologyCoefficientsSecondMap_epi_zero_of_power_torsion
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (hT : ∀ z : S.X₂, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    Epi (derivedLocalCohomologyCoefficientsSecondMap I hS 0) :=
  (AddCommGrpCat.epi_iff_surjective _).mpr
    (derivedLocalCohomologyModuleCoefficientsSecondMap_surjective_zero_of_power_torsion I hS hT)

end EtaleFundamentalGroups

end

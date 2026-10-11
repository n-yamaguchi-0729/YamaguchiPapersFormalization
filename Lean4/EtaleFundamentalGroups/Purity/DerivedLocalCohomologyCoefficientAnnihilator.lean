/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPowerTorsionAcyclic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Coefficient annihilators in local cohomology

A scalar annihilating the coefficients annihilates every local-cohomology
class, as is seen on its Ext representative. Along a coefficient short
exact sequence, an annihilator of the quotient and an annihilator of the
middle local-cohomology group multiply to annihilate the first group.
This is the induction step for truncating an injective complex whose
intermediate homology modules have scalar annihilators.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits Opposite

variable {R : Type u} [CommRing R]

/-- A scalar annihilating a coefficient module annihilates its local
cohomology with any support, in every degree. -/
theorem derivedLocalCohomologyModule_smul_eq_zero_of_coefficients
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) (a : R)
    (ha : ∀ m : M, a • m = 0)
    (z : derivedLocalCohomologyModule I M n) : a • z = 0 := by
  have haid : a • 𝟙 M = 0 := by
    ext m
    exact ha m
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨k, α, hα⟩ :=
    Concrete.colimit_exists_rep (derivedLocalCohomologyPowersDiagram I M n) z
  rcases k with ⟨⟨s⟩⟩
  let α' : CategoryTheory.Abelian.Ext.{u}
      (ModuleCat.of R (R ⧸ I ^ s)) M n := α
  have hαzero : a • α' = 0 := by
    rw [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀, haid,
      CategoryTheory.Abelian.Ext.mk₀_zero, CategoryTheory.Abelian.Ext.comp_zero]
  have hrep : derivedLocalCohomologyModuleι I M n s α' = z := hα
  rw [← hrep, ← (derivedLocalCohomologyModuleι I M n s).map_smul a α',
    hαzero, map_zero]

/-- In a coefficient short exact sequence, an annihilator of the last
module and an annihilator of the middle cohomology multiply to annihilate
the first cohomology. -/
theorem derivedLocalCohomologyModule_mul_smul_eq_zero_of_shortExact
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (a b : R) (ha : ∀ m : S.X₃, a • m = 0)
    (hb : ∀ w : derivedLocalCohomologyModule I S.X₂ (n + 1), b • w = 0)
    (z : derivedLocalCohomologyModule I S.X₁ (n + 1)) :
    (a * b) • z = 0 := by
  let f := derivedLocalCohomologyModuleCoefficientsFirstMap I hS (n + 1)
  let δ := derivedLocalCohomologyModuleCoefficientsConnectingMap I hS n
  have hf : f (b • z) = 0 := by
    rw [map_smul]
    exact hb (f z)
  obtain ⟨w, hw⟩ :=
    (derivedLocalCohomologyModuleCoefficients_afterConnecting_exact I hS n
      (b • z)).mp hf
  calc
    (a * b) • z = a • (b • z) := mul_smul a b z
    _ = a • δ w := congrArg (fun v => a • v) hw.symm
    _ = δ (a • w) := (map_smul δ a w).symm
    _ = 0 := by
      rw [derivedLocalCohomologyModule_smul_eq_zero_of_coefficients I S.X₃ n a ha,
        map_zero]

/-- For a short exact sequence with injective middle term, an annihilator
in degree `n` of the last coefficient annihilates degree `n + 1` of the
first coefficient. This is scalar-compatible dimension shifting. -/
theorem derivedLocalCohomologyModule_smul_eq_zero_of_injective_middle
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Injective R S.X₂] (n : ℕ) (a : R)
    (ha : ∀ w : derivedLocalCohomologyModule I S.X₃ n, a • w = 0)
    (z : derivedLocalCohomologyModule I S.X₁ (n + 1)) : a • z = 0 := by
  let δ := derivedLocalCohomologyModuleCoefficientsConnectingMap I hS n
  let : Subsingleton (derivedLocalCohomologyModule I S.X₂ (n + 1)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (derivedLocalCohomology_isZero_succ_of_injective I S.X₂ n)
  obtain ⟨w, hw⟩ :=
    (derivedLocalCohomologyModuleCoefficients_afterConnecting_exact I hS n z).mp
      (Subsingleton.elim _ _)
  calc
    a • z = a • δ w := congrArg (fun v => a • v) hw.symm
    _ = δ (a • w) := (map_smul δ a w).symm
    _ = 0 := by rw [ha w, map_zero]

end EtaleFundamentalGroups

end

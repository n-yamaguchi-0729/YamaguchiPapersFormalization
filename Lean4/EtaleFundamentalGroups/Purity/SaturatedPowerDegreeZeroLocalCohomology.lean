/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.CompleteLocalSaturatedPowers
import EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.MaximalIdealTorsionQuotient
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degree-zero local cohomology of saturated-power quotients

The quotient by a saturated ideal is canonically the quotient of the
original module by its maximal-ideal-primary component. The first
isomorphism theorem identifies these actual quotients before the
ideal is specialized to a power. The absence of power torsion then
makes degree-zero maximal-ideal local cohomology vanish.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Quotienting by the contracted primary component gives the actual
quotient of the original module by that component. -/
def maximalIdealSaturationQuotientEquiv (I : Ideal R) :
    (R ⧸ maximalIdealSaturation I) ≃ₗ[R]
      ((R ⧸ I) ⧸ Ideal.primaryComponent (R ⧸ I) (maximalIdeal R)) := by
  let T : Submodule R (R ⧸ I) := Ideal.primaryComponent (R ⧸ I) (maximalIdeal R)
  let f : R →ₗ[R] (R ⧸ I) ⧸ T := T.mkQ.comp I.mkQ
  have hf : Function.Surjective f := T.mkQ_surjective.comp I.mkQ_surjective
  have hker : maximalIdealSaturation I = LinearMap.ker f := by
    simp only [f, LinearMap.ker_comp, Submodule.ker_mkQ, maximalIdealSaturation, T]
  exact (Submodule.quotEquivOfEq (maximalIdealSaturation I) (LinearMap.ker f) hker).trans
    (f.quotKerEquivOfSurjective hf)

/-- Quotients by maximal-ideal-saturated powers have no degree-zero
maximal-ideal local cohomology. -/
theorem derivedLocalCohomology_maximalIdeal_saturatedPower_quotient_zero
    [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    IsZero (derivedLocalCohomology (maximalIdeal R)
      (ModuleCat.of R (R ⧸ maximalIdealSaturatedPower I n)) 0) := by
  let M : ModuleCat.{u} R := ModuleCat.of R (R ⧸ maximalIdealSaturatedPower I n)
  let e₀ := derivedLocalCohomologyZeroToModule (maximalIdeal R) M
  let e : M ≃ₗ[R]
      ((R ⧸ I ^ n) ⧸ Ideal.primaryComponent (R ⧸ I ^ n) (maximalIdeal R)) :=
    maximalIdealSaturationQuotientEquiv (I ^ n)
  have hEval (z : derivedLocalCohomologyModule (maximalIdeal R) M 0) : e₀ z = 0 := by
    apply e.injective
    rw [map_zero]
    apply eq_zero_of_idealPower_torsion_quotient_primaryComponent (maximalIdeal R)
    obtain ⟨k, hk⟩ := (mem_range_derivedLocalCohomologyZeroToModule_iff
      (maximalIdeal R) M (e₀ z)).mp (LinearMap.mem_range_self e₀ z)
    refine ⟨k, fun a ha => ?_⟩
    rw [← map_smul, hk a ha, map_zero]
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  refine ⟨fun z w => ?_⟩
  exact (derivedLocalCohomologyZeroToModule_injective (maximalIdeal R) M)
    ((hEval z).trans (hEval w).symm)

end EtaleFundamentalGroups.Purity

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPowerTorsionAcyclic
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalAnnihilated
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# Removing ideal-power torsion from coefficient modules

Degree-zero local cohomology has image equal to the primary component
of the coefficient module.  In a short exact coefficient sequence whose
first term is ideal-power torsion, the positive-degree second maps are
linear equivalences, since both neighboring cohomology groups vanish.
-/

noncomputable section

open CategoryTheory Limits

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- The degree-zero evaluation image is the primary component for the
support ideal. -/
theorem range_derivedLocalCohomologyZeroToModule
    (I : Ideal R) (M : ModuleCat.{u} R) :
    LinearMap.range (derivedLocalCohomologyZeroToModule I M) =
      Ideal.primaryComponent M I := by
  ext z
  simp only [mem_range_derivedLocalCohomologyZeroToModule_iff,
    Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff,
    SetLike.coe_sort_coe, Subtype.forall]

/-- Evaluation identifies degree-zero local cohomology with the concrete
ideal-primary component of its coefficient module. -/
def derivedLocalCohomologyZeroEquivPrimaryComponent
    (I : Ideal R) (M : ModuleCat.{u} R) :
    derivedLocalCohomologyModule I M 0 ≃ₗ[R] Ideal.primaryComponent M I := by
  let f : derivedLocalCohomologyModule I M 0 →ₗ[R] Ideal.primaryComponent M I :=
    LinearMap.codRestrict (Ideal.primaryComponent M I)
      (derivedLocalCohomologyZeroToModule I M) (fun z => by
        rw [← range_derivedLocalCohomologyZeroToModule I M]
        exact LinearMap.mem_range_self (derivedLocalCohomologyZeroToModule I M) z)
  apply LinearEquiv.ofBijective f
  constructor
  · intro z w h
    exact (derivedLocalCohomologyZeroToModule_injective I M) (congrArg Subtype.val h)
  · intro z
    have hz : (z : M) ∈ LinearMap.range (derivedLocalCohomologyZeroToModule I M) := by
      rw [range_derivedLocalCohomologyZeroToModule I M]
      exact z.property
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, Subtype.ext hw⟩

/-- The degree-zero equivalence retains the original evaluation map. -/
theorem derivedLocalCohomologyZeroEquivPrimaryComponent_apply_val
    (I : Ideal R) (M : ModuleCat.{u} R)
    (z : derivedLocalCohomologyModule I M 0) :
    (derivedLocalCohomologyZeroEquivPrimaryComponent I M z : M) =
      derivedLocalCohomologyZeroToModule I M z :=
  rfl

/-- Removing an ideal-power torsion first coefficient term induces a
bijection in every positive cohomological degree. -/
theorem derivedLocalCohomologyModuleCoefficientsSecondMap_bijective_succ_of_power_torsion
    [IsNoetherianRing R]
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (hT : ∀ z : S.X₁, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z = 0) (n : ℕ) :
    Function.Bijective (derivedLocalCohomologyModuleCoefficientsSecondMap I hS (n + 1)) := by
  have hmono : Mono (derivedLocalCohomologyCoefficientsSecondMap I hS (n + 1)) :=
    derivedLocalCohomologyCoefficientsSecondMap_mono_of_first_isZero I hS (n + 1)
      (derivedLocalCohomology_isZero_succ_of_power_torsion I S.X₁ hT n)
  have hepi : Epi (derivedLocalCohomologyCoefficientsSecondMap I hS (n + 1)) :=
    derivedLocalCohomologyCoefficientsSecondMap_epi_of_next_first_isZero I hS (n + 1)
      (derivedLocalCohomology_isZero_succ_of_power_torsion I S.X₁ hT (n + 1))
  exact ⟨(AddCommGrpCat.mono_iff_injective _).mp hmono,
    (AddCommGrpCat.epi_iff_surjective _).mp hepi⟩

/-- The linear equivalence on positive-degree local cohomology obtained
after removing ideal-power torsion coefficients. -/
def derivedLocalCohomologyModuleCoefficientsSecondEquiv_succ_of_power_torsion
    [IsNoetherianRing R]
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (hT : ∀ z : S.X₁, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z = 0) (n : ℕ) :
    derivedLocalCohomologyModule I S.X₂ (n + 1) ≃ₗ[R]
      derivedLocalCohomologyModule I S.X₃ (n + 1) :=
  LinearEquiv.ofBijective (derivedLocalCohomologyModuleCoefficientsSecondMap I hS (n + 1))
    (derivedLocalCohomologyModuleCoefficientsSecondMap_bijective_succ_of_power_torsion I hS hT n)

end EtaleFundamentalGroups

end

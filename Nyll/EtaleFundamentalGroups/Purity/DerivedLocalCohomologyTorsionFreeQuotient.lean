/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionQuotient
import Nyll.EtaleFundamentalGroups.Purity.MaximalIdealTorsionQuotient
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# Local cohomology after removing the primary component

The quotient by the maximal-ideal-primary component has zero degree-zero
local cohomology: evaluation is injective, and every value is a power-torsion
vector in a quotient containing no such nonzero vector.  In positive degrees
the inclusion of the primary component and its quotient give a concrete
linear equivalence through the coefficient long exact sequence.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits IsLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Removing the maximal-ideal-primary component of a finite coefficient
module makes its degree-zero maximal-support local cohomology vanish. -/
theorem derivedLocalCohomology_maximalIdeal_isZero_zero_quotient_primaryComponent
    [IsLocalRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsZero (derivedLocalCohomology (maximalIdeal R)
      (ModuleCat.of R (M ⧸ Ideal.primaryComponent M (maximalIdeal R))) 0) := by
  let Q : ModuleCat.{u} R :=
    ModuleCat.of R (M ⧸ Ideal.primaryComponent M (maximalIdeal R))
  have hEval (z : derivedLocalCohomologyModule (maximalIdeal R) Q 0) :
      derivedLocalCohomologyZeroToModule (maximalIdeal R) Q z = 0 :=
    Purity.eq_zero_of_idealPower_torsion_quotient_primaryComponent (M := M)
      (maximalIdeal R) (derivedLocalCohomologyZeroToModule (maximalIdeal R) Q z)
      ((mem_range_derivedLocalCohomologyZeroToModule_iff
        (maximalIdeal R) Q _).mp
          (LinearMap.mem_range_self (derivedLocalCohomologyZeroToModule (maximalIdeal R) Q) z))
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  refine ⟨fun z w => ?_⟩
  exact (derivedLocalCohomologyZeroToModule_injective (maximalIdeal R) Q)
    ((hEval z).trans (hEval w).symm)

/-- Quotienting by the ideal-primary component preserves all positive
degrees of local cohomology, via the concrete coefficient quotient map. -/
noncomputable def derivedLocalCohomologyModuleEquiv_succ_quotient_primaryComponent
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    derivedLocalCohomologyModule I M (n + 1) ≃ₗ[R]
      derivedLocalCohomologyModule I
        (ModuleCat.of R (M ⧸ Ideal.primaryComponent M I)) (n + 1) := by
  let T : Submodule R M := Ideal.primaryComponent M I
  let S : ShortComplex (ModuleCat.{u} R) :=
    ModuleCat.shortComplexOfCompEqZero T.subtype T.mkQ
      (LinearMap.exact_subtype_mkQ T).linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    ModuleCat.shortComplex_shortExact S (LinearMap.exact_subtype_mkQ T)
      T.subtype_injective T.mkQ_surjective
  have hT : ∀ z : T, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z = 0 := by
    intro z
    obtain ⟨k, hk⟩ :=
      (Ideal.primaryComponent_mem (M := M) (I := I) (z : M)).mp z.property
    refine ⟨k, ?_⟩
    intro a ha
    apply Subtype.ext
    change a • (z : M) = (0 : M)
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := M)
      ((I ^ k : Ideal R) : Set R) (z : M)).mp hk ⟨a, ha⟩
  exact derivedLocalCohomologyModuleCoefficientsSecondEquiv_succ_of_power_torsion I hS hT n

end EtaleFundamentalGroups

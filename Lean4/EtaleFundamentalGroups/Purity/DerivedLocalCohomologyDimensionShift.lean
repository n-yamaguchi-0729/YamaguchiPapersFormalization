/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPowerTorsionAcyclic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Exact.Basic

/-!
# Dimension shifting for derived local cohomology

The coefficient connecting map is surjective when the middle module is
injective, and bijective when its source cohomology degree is positive.
These are consequences of the actual coefficient long exact sequence and
vanishing of positive Ext groups for injective modules.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- Injective middle coefficients make every connecting map surjective. -/
theorem derivedLocalCohomologyConnecting_surjective_of_injective
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Injective R S.X₂] (n : ℕ) :
    Function.Surjective (derivedLocalCohomologyModuleCoefficientsConnectingMap I hS n) := by
  let : Subsingleton (derivedLocalCohomologyModule I S.X₂ (n + 1)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (derivedLocalCohomology_isZero_succ_of_injective I S.X₂ n)
  intro z
  exact (derivedLocalCohomologyModuleCoefficients_afterConnecting_exact I hS n z).mp
    (Subsingleton.elim _ _)

/-- In positive source degree the same connecting map is also injective. -/
theorem derivedLocalCohomologyConnecting_bijective_succ_of_injective
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Injective R S.X₂] (n : ℕ) :
    Function.Bijective
      (derivedLocalCohomologyModuleCoefficientsConnectingMap I hS (n + 1)) := by
  refine ⟨?_, derivedLocalCohomologyConnecting_surjective_of_injective I hS (n + 1)⟩
  let : Subsingleton (derivedLocalCohomologyModule I S.X₂ (n + 1)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (derivedLocalCohomology_isZero_succ_of_injective I S.X₂ n)
  apply (LinearMap.injective_iff_eq_zero_of_exact
    (derivedLocalCohomologyModuleCoefficients_beforeConnecting_exact I hS (n + 1))).mpr
  apply LinearMap.ext
  intro z
  rw [Subsingleton.elim z 0, map_zero]
  rfl

end EtaleFundamentalGroups.Purity

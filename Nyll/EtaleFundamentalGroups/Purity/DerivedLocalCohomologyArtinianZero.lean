/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.FinitePowerTorsionLength
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite length in degree zero

Degree-zero local cohomology embeds in its finite coefficient module.
Noetherianity makes it finite, and its maximal-ideal-power torsion then
gives finite length.  This is the base of the Artinianness induction.
-/

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Degree-zero local cohomology of a finite module over a Noetherian
local ring has finite length. -/
theorem isFiniteLength_derivedLocalCohomologyModule_maximalIdeal_zero
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLength R
      (derivedLocalCohomologyModule (IsLocalRing.maximalIdeal R) M 0) := by
  let : IsNoetherian R
      (derivedLocalCohomologyModule (IsLocalRing.maximalIdeal R) M 0) :=
    isNoetherian_of_injective
      (derivedLocalCohomologyZeroToModule (IsLocalRing.maximalIdeal R) M)
      (derivedLocalCohomologyZeroToModule_injective (IsLocalRing.maximalIdeal R) M)
  exact Purity.isFiniteLength_of_finite_of_maximalIdealPower_torsion
    (derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero
      (IsLocalRing.maximalIdeal R) M 0)

/-- In particular degree-zero maximal-support local cohomology of a
finite module is Artinian. -/
theorem isArtinian_derivedLocalCohomologyModule_maximalIdeal_zero
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsArtinian R
      (derivedLocalCohomologyModule (IsLocalRing.maximalIdeal R) M 0) :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp
    (isFiniteLength_derivedLocalCohomologyModule_maximalIdeal_zero M)).2

end EtaleFundamentalGroups

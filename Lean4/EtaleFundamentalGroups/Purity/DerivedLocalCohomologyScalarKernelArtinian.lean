/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.CompleteLocalPowerTorsionArtinian
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Regular.Category

/-!
# Artinianness from a regular coefficient quotient

For a scalar regular on the coefficient module, the connecting map from
the preceding cohomology of its quotient has image equal to the scalar
kernel on the next local-cohomology module.  Artinianness of that quotient
cohomology therefore makes the scalar kernel Artinian.  The actual
ideal-power torsion of local cohomology then proves Artinianness over a
complete Noetherian local ring.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [IsAdicComplete (maximalIdeal R) R]

/-- If a scalar in the maximal ideal is regular on the coefficients,
Artinianness in degree `n` of the coefficient quotient implies
Artinianness in degree `n + 1` of the original coefficients. -/
theorem isArtinian_derivedLocalCohomologyModule_succ_of_regular_smulQuotient
    (M : ModuleCat.{u} R) (x : R) (hx : x ∈ maximalIdeal R)
    (hxreg : IsSMulRegular M x) (n : ℕ)
    [IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R)
      (ModuleCat.smulShortComplex M x).X₃ n)] :
    IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R) M (n + 1)) := by
  let δ : derivedLocalCohomologyModule (maximalIdeal R)
      (ModuleCat.smulShortComplex M x).X₃ n →ₗ[R]
        derivedLocalCohomologyModule (maximalIdeal R) M (n + 1) :=
    derivedLocalCohomologyModuleCoefficientsConnectingMap
      (maximalIdeal R) hxreg.smulShortComplex_shortExact n
  have hexact := derivedLocalCohomologyModuleCoefficients_afterConnecting_exact
    (maximalIdeal R) hxreg.smulShortComplex_shortExact n
  rw [derivedLocalCohomologyModuleCoefficientsFirstMap_smulShortComplex
    (maximalIdeal R) M (n + 1) x hxreg] at hexact
  change Function.Exact δ
    (x • (LinearMap.id : derivedLocalCohomologyModule (maximalIdeal R) M (n + 1) →ₗ[R]
      derivedLocalCohomologyModule (maximalIdeal R) M (n + 1))) at hexact
  have hker : LinearMap.ker
      (x • (LinearMap.id : derivedLocalCohomologyModule (maximalIdeal R) M (n + 1) →ₗ[R]
        derivedLocalCohomologyModule (maximalIdeal R) M (n + 1))) =
        LinearMap.range δ := hexact.linearMap_ker_eq
  let : IsArtinian R (LinearMap.ker
      (x • (LinearMap.id : derivedLocalCohomologyModule (maximalIdeal R) M (n + 1) →ₗ[R]
        derivedLocalCohomologyModule (maximalIdeal R) M (n + 1)))) := by
    rw [hker]
    exact isArtinian_range δ
  apply isArtinian_of_maximalIdealPower_torsion_of_artinian_scalarKernel x hx
  exact derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero
    (maximalIdeal R) M (n + 1)

end EtaleFundamentalGroups.Purity

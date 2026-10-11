/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalAnnihilated
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Regular.Category

/-!
# Scalar quotients of local cohomology

For a regular scalar, the coefficient long exact sequence identifies
local cohomology of the scalar quotient with the quotient of local
cohomology by that scalar whenever the next cohomological degree vanishes.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits
open scoped Pointwise

variable {R : Type u} [CommRing R]

/-- If the next local-cohomology group vanishes, passing to the quotient
by a regular scalar commutes with local cohomology in the current degree. -/
noncomputable def derivedLocalCohomologyModuleScalarQuotientEquiv
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (x : R) (hx : IsSMulRegular M x)
    (hzero : IsZero (derivedLocalCohomology I M (n + 1))) :
    (derivedLocalCohomologyModule I M n ⧸
      x • (⊤ : Submodule R (derivedLocalCohomologyModule I M n))) ≃ₗ[R]
        derivedLocalCohomologyModule I (ModuleCat.smulShortComplex M x).X₃ n := by
  let g : derivedLocalCohomologyModule I M n →ₗ[R]
      derivedLocalCohomologyModule I (ModuleCat.smulShortComplex M x).X₃ n :=
    derivedLocalCohomologyModuleCoefficientsSecondMap
      I hx.smulShortComplex_shortExact n
  have hepi : Epi (derivedLocalCohomologyCoefficientsSecondMap
      I hx.smulShortComplex_shortExact n) :=
    derivedLocalCohomologyCoefficientsSecondMap_epi_of_next_first_isZero
      I hx.smulShortComplex_shortExact n hzero
  have hg : Function.Surjective g :=
    (AddCommGrpCat.epi_iff_surjective _).mp hepi
  have hexact : Function.Exact
      (x • (LinearMap.id : derivedLocalCohomologyModule I M n →ₗ[R]
        derivedLocalCohomologyModule I M n)) g := by
    have h := derivedLocalCohomologyModuleCoefficients_sameDegree_exact
      I hx.smulShortComplex_shortExact n
    rw [derivedLocalCohomologyModuleCoefficientsFirstMap_smulShortComplex
      I M n x hx] at h
    change Function.Exact
      (x • (LinearMap.id : derivedLocalCohomologyModule I M n →ₗ[R]
        derivedLocalCohomologyModule I M n)) g at h
    exact h
  have hker : LinearMap.ker g =
      x • (⊤ : Submodule R (derivedLocalCohomologyModule I M n)) := by
    rw [hexact.linearMap_ker_eq]
    change LinearMap.range
        (LinearMap.lsmul R (derivedLocalCohomologyModule I M n) x) = _
    exact (LinearMap.exact_lsmul_mkQ_smul_top
      (derivedLocalCohomologyModule I M n) x).linearMap_ker_eq.symm.trans
        (Submodule.ker_mkQ _)
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective g hg)

/-- The scalar-quotient equivalence is induced by the second coefficient
map on representatives. -/
theorem derivedLocalCohomologyModuleScalarQuotientEquiv_apply_mk
    (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (x : R) (hx : IsSMulRegular M x)
    (hzero : IsZero (derivedLocalCohomology I M (n + 1)))
    (z : derivedLocalCohomologyModule I M n) :
    derivedLocalCohomologyModuleScalarQuotientEquiv I M n x hx hzero
        (Submodule.Quotient.mk z) =
      derivedLocalCohomologyModuleCoefficientsSecondMap I hx.smulShortComplex_shortExact n z := by
  let g : derivedLocalCohomologyModule I M n →ₗ[R]
      derivedLocalCohomologyModule I (ModuleCat.smulShortComplex M x).X₃ n :=
    derivedLocalCohomologyModuleCoefficientsSecondMap
      I hx.smulShortComplex_shortExact n
  have hepi : Epi (derivedLocalCohomologyCoefficientsSecondMap
      I hx.smulShortComplex_shortExact n) :=
    derivedLocalCohomologyCoefficientsSecondMap_epi_of_next_first_isZero
      I hx.smulShortComplex_shortExact n hzero
  have hg : Function.Surjective g :=
    (AddCommGrpCat.epi_iff_surjective _).mp hepi
  change (g.quotKerEquivOfSurjective hg) (Submodule.Quotient.mk z) = g z
  exact g.quotKerEquivOfSurjective_apply_mk hg z

end EtaleFundamentalGroups

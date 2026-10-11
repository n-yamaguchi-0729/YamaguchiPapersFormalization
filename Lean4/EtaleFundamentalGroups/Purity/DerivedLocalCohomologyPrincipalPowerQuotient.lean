/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.QuotSMulTop

/-!
# Principal ideal-power quotients

For a principal ideal `(x)`, the quotient by its `n`-th ideal power is
canonically the quotient by the submodule `x ^ n R`.  This file records that
identification and its compatibility with the standard transition maps between
power quotients.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups

universe u

section

variable {R : Type u} [CommRing R]

/-- The submodule underlying `(x) ^ n` is `x ^ n R`. -/
theorem principalIdealPower_submodule_eq_smulTop (x : R) (n : ℕ) :
    ((Ideal.span {x}) ^ n : Submodule R R) =
      x ^ n • (⊤ : Submodule R R) := by
  rw [Ideal.span_singleton_pow]
  calc
    (Ideal.span {x ^ n} : Submodule R R) =
        Ideal.span {x ^ n} • (⊤ : Submodule R R) := by
      rw [smul_eq_mul, Ideal.mul_top]
    _ = x ^ n • (⊤ : Submodule R R) :=
      Submodule.ideal_span_singleton_smul (x ^ n) ⊤

/-- The quotient by `(x) ^ n` as an ideal is canonically the quotient by
the submodule `x ^ n R`. -/
def principalPowerQuotientLinearEquiv (x : R) (n : ℕ) :
    (R ⧸ (Ideal.span {x}) ^ n) ≃ₗ[R] QuotSMulTop (x ^ n) R :=
  Submodule.quotEquivOfEq _ _
    (principalIdealPower_submodule_eq_smulTop x n)

/-- The standard quotient map from the `m`-th principal ideal-power quotient
to the `n`-th one, for `n ≤ m`. -/
def principalPowerQuotientTransition (x : R) {n m : ℕ} (h : n ≤ m) :
    (R ⧸ (Ideal.span {x}) ^ m) →ₗ[R]
      (R ⧸ (Ideal.span {x}) ^ n) :=
  Submodule.mapQ _ _ LinearMap.id (Ideal.pow_le_pow_right h)

/-- The preceding map is exactly the map used by the ideal-powers quotient
diagram defining local cohomology. -/
theorem principalPowerQuotientTransition_eq_ringModIdeals_map
    (x : R) {n m : ℕ} (h : n ≤ m) :
    ModuleCat.ofHom (principalPowerQuotientTransition x h) =
      (localCohomology.ringModIdeals
        (localCohomology.idealPowersDiagram (Ideal.span {x}))).map
          (CategoryTheory.homOfLE h).op := by
  rfl

/-- The corresponding standard quotient map between quotients by the
submodules `x ^ m R` and `x ^ n R`. -/
def quotSMulTopPowerTransition (x : R) {n m : ℕ} (h : n ≤ m) :
    QuotSMulTop (x ^ m) R →ₗ[R] QuotSMulTop (x ^ n) R :=
  let hle : x ^ m • (⊤ : Submodule R R) ≤
      x ^ n • (⊤ : Submodule R R) := by
    rw [← principalIdealPower_submodule_eq_smulTop x m,
      ← principalIdealPower_submodule_eq_smulTop x n]
    exact Ideal.pow_le_pow_right h
  Submodule.mapQ _ _ LinearMap.id (by simpa using hle)

/-- The canonical identifications of principal ideal-power quotients commute
with their standard transition maps. -/
theorem principalPowerQuotientLinearEquiv_transition (x : R)
    {n m : ℕ} (h : n ≤ m) :
    (quotSMulTopPowerTransition x h).comp
        (principalPowerQuotientLinearEquiv x m).toLinearMap =
      (principalPowerQuotientLinearEquiv x n).toLinearMap.comp
        (principalPowerQuotientTransition x h) := by
  ext
  rfl

end

end EtaleFundamentalGroups

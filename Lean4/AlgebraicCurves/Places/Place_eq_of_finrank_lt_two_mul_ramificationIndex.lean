/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eq_of_finrank_lt_two_mul_ramificationIndex.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import AlgebraicCurves.Places.Place_inertiaDeg_pos_of_finiteDimensional

/-!
# Place eq of finrank lt two mul ramification Index
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_eq_of_finrank_lt_two_mul_ramificationIndex

open AlgebraicCurve

namespace S09CDZ

section Counting

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F
  F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

theorem place_eq_of_two_mul_le_ramificationIndex {U U' : Place K F'} (hres : U'.restrict F =
  U.restrict F) {m : ℕ}
    (hm : Module.finrank F F' < 2 * m) (hU : m ≤ U.ramificationIndex F) (hU' : m ≤
      U'.ramificationIndex F) : U = U' := by
  classical
  by_contra hne
  have h := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank (U.restrict F) {U, U'} (by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rfl
    · rw [Finset.mem_singleton.mp hw]; exact hres)
  rw [Finset.sum_pair hne] at h
  have hf : 0 < U.inertiaDeg F := Place.inertiaDeg_pos_of_finiteDimensional (F := F) U
  have hf' : 0 < U'.inertiaDeg F := Place.inertiaDeg_pos_of_finiteDimensional (F := F) U'
  have h1 : (m : ℤ) ≤ (U.ramificationIndex F : ℤ) * (U.inertiaDeg F : ℤ) := by
    have : (m : ℤ) ≤ U.ramificationIndex F := by exact_mod_cast hU
    nlinarith [show (1 : ℤ) ≤ U.inertiaDeg F by exact_mod_cast hf]
  have h2 : (m : ℤ) ≤ (U'.ramificationIndex F : ℤ) * (U'.inertiaDeg F : ℤ) := by
    have : (m : ℤ) ≤ U'.ramificationIndex F := by exact_mod_cast hU'
    nlinarith [show (1 : ℤ) ≤ U'.inertiaDeg F by exact_mod_cast hf']
  have hm' : (Module.finrank F F' : ℤ) < 2 * m := by exact_mod_cast hm
  omega

end Counting

end S09CDZ

theorem _root_.AlgebraicCurve.Place.eq_of_finrank_lt_two_mul_ramificationIndex {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {U U' : Place K F'} (hres : U'.restrict F =
  U.restrict F) {m : ℕ} (hm : Module.finrank F F' < 2 * m) (hU : m ≤ U.ramificationIndex F) (hU' :
  m ≤ U'.ramificationIndex F) : U = U' :=
  S09CDZ.place_eq_of_two_mul_le_ramificationIndex hres hm hU hU'
end AlgebraicCurves.Places.Proofs.Place_eq_of_finrank_lt_two_mul_ramificationIndex
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

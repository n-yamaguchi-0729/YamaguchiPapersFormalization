/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.OverDVR
import Mathlib.RingTheory.Algebraic.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Place ord eq zero of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_eq_zero_of_isAlgebraic

noncomputable section
open Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace FF2R0
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)

private theorem mem_of_isAlgebraic {x : F} (hx : IsAlgebraic K x) : x ∈ v.toValuationSubring := by
  have hint : IsIntegral K x := hx.isIntegral
  refine v.mem_of_eval_monic_eq_zero (P := (minpoly K x).map (algebraMap K F)) ((minpoly.monic
    hint).map _)
    (fun i => ?_) ?_
  · rw [coeff_map]; exact v.algebraMap_mem' _
  · rw [eval_map_algebraMap, minpoly.aeval]

theorem ord_eq_zero_of_isAlgebraic' {x : F} (hx : IsAlgebraic K x) : v.ord x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0, v.ord_zero]
  · let u : v.toValuationSubringˣ :=
      { val := ⟨x, mem_of_isAlgebraic v hx⟩
        inv := ⟨x⁻¹, mem_of_isAlgebraic v hx.inv⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hx0)
        inv_val := Subtype.ext (inv_mul_cancel₀ hx0) }
    exact v.ord_coe_unit u

end AlgebraicCurve.Place.FF2R0

theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic {K F : Type*} [Field K] [Field F]
  [Algebra K F] (v : AlgebraicCurve.Place K F) {x : F} (hx : IsAlgebraic K x) :
    v.ord x = 0 :=
  AlgebraicCurve.Place.FF2R0.ord_eq_zero_of_isAlgebraic' v hx

end
end AlgebraicCurves.Places.Proofs.Place_ord_eq_zero_of_isAlgebraic
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

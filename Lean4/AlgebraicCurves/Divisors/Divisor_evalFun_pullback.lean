/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Place_evalAt_norm_eq_prod_fiber
import AlgebraicCurves.Places.Place_pairwiseDisjoint_fiber
import AlgebraicCurves.Divisors.Divisor_support_pullback_subset

/-!
# Divisor eval Fun pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_pullback
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

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.evalFun_pullback {K F F' : Type*} [Field K] [Field F] [Field
  F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (E : Divisor K F)
  (hrat : ∀ v ∈ E.support, Place.IsRational v) (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F',
  Place.IsRational w) (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) : Divisor.evalFun f
  (Divisor.pullback F' E) = Divisor.evalFun (Algebra.norm F f) E := by
  classical
  rw [show evalFun f (pullback F' E)
      = ∏ w ∈ E.support.biUnion (fun v => v.fiber F'), w.evalAt f ^ (pullback F' E) w from
    Finsupp.prod_of_support_subset _ (AlgebraicCurve.Divisor.support_pullback_subset E)
      (fun w n => w.evalAt f ^ n) fun w _ => zpow_zero _,
    Finset.prod_biUnion (AlgebraicCurve.Place.pairwiseDisjoint_fiber E.support), evalFun_def]
  refine Finset.prod_congr rfl fun v hv => ?_
  calc
    ∏ w ∈ v.fiber F', w.evalAt f ^ (pullback F' E) w
        = ∏ w ∈ v.fiber F', (w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v := by
          refine Finset.prod_congr rfl fun w hw => ?_
          rw [pullback_apply, Place.mem_fiber.mp hw, ← zpow_mul]
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v :=
          Finset.prod_zpow _ _ _
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F)) ^ E v := by
          refine congrArg (· ^ E v) (Finset.prod_congr rfl fun w _ => ?_)
          rw [zpow_natCast]
    _ = v.evalAt (Algebra.norm F f) ^ E v := by
          rw [AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber v f hf (hrat v hv) (hratw v hv) (hord
            v hv)]
end AlgebraicCurves.Divisors.Proofs.Divisor_evalFun_pullback
end ProofImplementation

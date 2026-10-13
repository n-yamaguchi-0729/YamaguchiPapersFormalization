/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.IntegerLocalizationValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Parameters supplied by two integral section equations

The concrete equations `w` and `v-u*w` form a weakly regular sequence in
`ℤ[w]` when `v` is nonzero: modulo `w`, multiplication by the second
equation is multiplication by the nonzero integer `v`. When `p` divides
`v`, both equations lie in `(p,w)`, so their images form a regular sequence
in that localization and then in the actual projective stalk.

If `v_p(v)=1`, the previously calculated intersection quotient has length
one. Its ideal is therefore the maximal ideal of the local ring. The two
actual equation germs consequently form a regular system of parameters.

This is the normalized two-section local calculation needed for the
normal-crossings assertion in Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The finite-divisor criterion and its comparison with base change to `ℤ_p`
are separate assertions.
-/

noncomputable section

open scoped Polynomial Pointwise

namespace ShimizuYamaguchi26BranchedCoverings

/-- The germs of `w` and `v-u*w` at `(p,w)` form a regular sequence when
`v` is nonzero and divisible by `p`. -/
theorem integerProjectiveInfinitySectionEquations_isRegular
    (p : ℕ) [Fact p.Prime] (u v : ℤ) (hv : v ≠ 0) (hpv : (p : ℤ) ∣ v) :
    RingTheory.Sequence.IsRegular (IntegerProjectiveInfinityLocalRing p)
      ([infinityChartGermAt ℤ (integerInfinityChartPoint p) Polynomial.X,
        infinityChartGermAt ℤ (integerInfinityChartPoint p)
          (Polynomial.C v - Polynomial.C u * Polynomial.X)] :
        List (IntegerProjectiveInfinityLocalRing p)) := by
  apply sectionEquations_isRegular_infinityChart ℤ (integerInfinityChartPoint p) u v hv
  · change (Polynomial.X : ℤ[X]).coeff 0 ∈ IntegerPrimeIdeal p
    rw [Polynomial.coeff_X_zero]
    exact Ideal.zero_mem _
  · change (Polynomial.C v - Polynomial.C u * Polynomial.X).coeff 0 ∈ IntegerPrimeIdeal p
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero,
      Polynomial.coeff_mul_X_zero, sub_zero]
    exact Ideal.mem_span_singleton.mpr hpv

/-- When the local intersection multiplicity is one, the two concrete
section equations are a regular system of parameters in the actual
integral projective stalk. -/
theorem integerProjectiveInfinitySection_isRegularSystemOfParameters
    (p : ℕ) [Fact p.Prime] (u v : ℤ) (hv : v ≠ 0) (hval : padicValInt p v = 1) :
    AlgebraicGeometry.Scheme.IsRegularSystemOfParameters
      (![infinityChartGermAt ℤ (integerInfinityChartPoint p) Polynomial.X,
        infinityChartGermAt ℤ (integerInfinityChartPoint p)
          (Polynomial.C v - Polynomial.C u * Polynomial.X)] :
        Fin 2 → IntegerProjectiveInfinityLocalRing p) := by
  have hpv : (p : ℤ) ∣ v := by
    have h := padicValInt_dvd (p := p) v
    rw [hval, pow_one] at h
    exact h
  have hlength : Module.length (IntegerProjectiveInfinityLocalRing p)
      (IntegerProjectiveInfinityLocalRing p ⧸
        integerProjectiveInfinityIntersectionIdeal p u v) = 1 := by
    rw [integerProjectiveInfinityIntersection_length p u v hv, hval, Nat.cast_one]
  have hmaximal : integerProjectiveInfinityIntersectionIdeal p u v =
      IsLocalRing.maximalIdeal (IntegerProjectiveInfinityLocalRing p) := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hlength
    exact hlength
  let g : ℤ[X] →+* IntegerProjectiveInfinityLocalRing p :=
    infinityChartGermAt ℤ (integerInfinityChartPoint p)
  have hideal : Ideal.ofList
      [g Polynomial.X, g (Polynomial.C v - Polynomial.C u * Polynomial.X)] =
      integerProjectiveInfinityIntersectionIdeal p u v := by
    change Ideal.ofList
      [g Polynomial.X, g (Polynomial.C v - Polynomial.C u * Polynomial.X)] =
        (infinityIntersectionIdeal u v).map g
    rw [infinityIntersectionIdeal, Ideal.map_span, Set.image_pair,
      Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq, Ideal.span_insert]
  change RingTheory.Sequence.IsRegular (IntegerProjectiveInfinityLocalRing p)
      ([g Polynomial.X, g (Polynomial.C v - Polynomial.C u * Polynomial.X)] :
        List (IntegerProjectiveInfinityLocalRing p)) ∧
    Ideal.ofList [g Polynomial.X, g (Polynomial.C v - Polynomial.C u * Polynomial.X)] =
      IsLocalRing.maximalIdeal (IntegerProjectiveInfinityLocalRing p)
  exact ⟨integerProjectiveInfinitySectionEquations_isRegular p u v hv hpv,
    hideal.trans hmaximal⟩

end ShimizuYamaguchi26BranchedCoverings

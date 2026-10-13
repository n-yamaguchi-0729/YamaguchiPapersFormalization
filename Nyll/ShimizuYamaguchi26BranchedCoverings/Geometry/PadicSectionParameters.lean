/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.PadicIntegerValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ProjectiveInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionParameters
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Length

/-!
# Section equations in the actual p-adic projective stalk

At the infinity point over the closed point of `Spec ℤ_[p]`, the quotient
of the actual projective stalk by `w` and `v-u*w` has length `v_p(v)`.
Consequently its length agrees with the previously computed integer stalk
quotient. If this value is one, the concrete p-adic equation germs form a
regular system of parameters. Both conclusions use the actual p-adic ring,
not the localization of the integers at `p`.

These are the local algebra prerequisites for the p-adic normal-crossing
comparison in Shimizu and Yamaguchi, Lemma 2.3,
https://arxiv.org/abs/2608.15057v1. Identification with the pullback of every
original global section product is a further step.
-/

noncomputable section

open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- The two actual p-adic equation germs have intersection length `v_p(v)`. -/
theorem padicProjectiveInfinityIntersection_length
    (p : ℕ) [Fact p.Prime] (u v : ℤ) (hv : v ≠ 0) :
    Module.length (ProjectiveInfinityLocalRing ℤ_[p])
      (ProjectiveInfinityIntersectionAlgebra (u : ℤ_[p]) (v : ℤ_[p])) =
      (padicValInt p v : ℕ∞) := by
  rw [projectiveInfinityIntersection_length, padicInteger_addVal_eq_padicValInt p v hv]

/-- The two concrete equation germs have equal local intersection lengths
in the integer and p-adic projective local rings. -/
theorem padicProjectiveInfinityIntersection_length_eq_integer
    (p : ℕ) [Fact p.Prime] (u v : ℤ) (hv : v ≠ 0) :
    Module.length (ProjectiveInfinityLocalRing ℤ_[p])
      (ProjectiveInfinityIntersectionAlgebra (u : ℤ_[p]) (v : ℤ_[p])) =
    Module.length (IntegerProjectiveInfinityLocalRing p)
      (IntegerProjectiveInfinityLocalRing p ⧸
        integerProjectiveInfinityIntersectionIdeal p u v) := by
  rw [padicProjectiveInfinityIntersection_length p u v hv,
    integerProjectiveInfinityIntersection_length p u v hv]

/-- Valuation one supplies an actual regular parameter system in the
projective stalk over the p-adic integers. -/
theorem padicProjectiveInfinitySection_isRegularSystemOfParameters
    (p : ℕ) [Fact p.Prime] (u v : ℤ) (hv : v ≠ 0) (hval : padicValInt p v = 1) :
    AlgebraicGeometry.Scheme.IsRegularSystemOfParameters
      (![infinityChartGerm ℤ_[p] Polynomial.X,
        infinityChartGerm ℤ_[p]
          (Polynomial.C (v : ℤ_[p]) - Polynomial.C (u : ℤ_[p]) * Polynomial.X)] :
        Fin 2 → ProjectiveInfinityLocalRing ℤ_[p]) := by
  apply projectiveInfinitySection_isRegularSystemOfParameters (u : ℤ_[p]) (v : ℤ_[p])
    (Int.cast_ne_zero.mpr hv)
  rw [padicInteger_addVal_eq_padicValInt p v hv, hval, Nat.cast_one]

end ShimizuYamaguchi26BranchedCoverings

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.FieldTheory.RatFunc.Degree
import Lean.Elab.Tactic.Omega

/-!
# A linear polynomial is not a square in the rational function field

The discriminant in Proposition 2.5 of Shimizu--Yamaguchi has degree one.
Its nonsquareness follows from the integer degree of rational functions:
a nonzero square has even degree. This argument does not require a choice
of a root or an algebraic closure.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Proposition 2.5.
-/

noncomputable section

open Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- A nonconstant linear polynomial is not the square of a rational function. -/
theorem linearPolynomial_ne_square_ratFunc {K : Type*} [Field K]
    (a b : K) (ha : a ≠ 0) (r : RatFunc K) :
    algebraMap K[X] (RatFunc K) (C a * X + C b) ≠ r ^ 2 := by
  intro h
  have hdegree : RatFunc.intDegree (r ^ 2) = 1 := by
    simpa only [RatFunc.intDegree_polynomial, natDegree_linear ha, Int.ofNat_one] using
      congrArg RatFunc.intDegree h.symm
  have hr : r ≠ 0 := by
    intro hr
    rw [hr, zero_pow (by decide : (2 : ℕ) ≠ 0), RatFunc.intDegree_zero] at hdegree
    omega
  rw [pow_two, RatFunc.intDegree_mul hr hr] at hdegree
  omega

end ShimizuYamaguchi26BranchedCoverings

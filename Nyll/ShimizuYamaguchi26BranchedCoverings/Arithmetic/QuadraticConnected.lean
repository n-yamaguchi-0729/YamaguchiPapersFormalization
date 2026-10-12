/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticCover
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalFunctionNonsquare
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integrality of the quadratic covering algebra

The discriminant of the quadratic equation in Proposition 2.5 is the
nonconstant linear polynomial `ε * (v * t - u)`. Its image in `ℚ(t)` is not a
square, by degree. A root over `ℤ[t, 1 / (v * t - u)]` would make this image a
square. Thus the quadratic is irreducible. Unique factorization in this
localization then proves that its adjoined-root algebra is an integral domain.

The argument uses the explicit constant term from `QuadraticCover`; neither
irreducibility nor nonsquareness is an input assumption.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Proposition 2.5.
-/

noncomputable section

open Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- The usual inclusion of integral polynomials into the rational function field. -/
def integerPolynomialToRatFunc : ℤ[X] →+* RatFunc ℚ :=
  (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- The nonconstant signed boundary equation cannot be a square in `ℚ(t)`. -/
theorem signedBoundary_ne_square (u v ε : ℤ) (hε : ε ≠ 0) (hv : v ≠ 0)
    (r : RatFunc ℚ) :
    integerPolynomialToRatFunc (C ε * boundaryPolynomial u v) ≠ r ^ 2 := by
  have hmap : (C ε * boundaryPolynomial u v).map (Int.castRingHom ℚ) =
      C ((ε : ℚ) * (v : ℚ)) * X + C (-((ε : ℚ) * (u : ℚ))) := by
    simp only [boundaryPolynomial, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X]
    change C (ε : ℚ) * (C (v : ℚ) * X - C (u : ℚ)) = _
    simp only [map_neg, map_mul]
    ring
  change algebraMap ℚ[X] (RatFunc ℚ)
    ((C ε * boundaryPolynomial u v).map (Int.castRingHom ℚ)) ≠ r ^ 2
  rw [hmap]
  exact linearPolynomial_ne_square_ratFunc _ _
    (mul_ne_zero (Int.cast_ne_zero.mpr hε) (Int.cast_ne_zero.mpr hv)) r

/-- The canonical map from the affine coordinate ring to `ℚ(t)`. -/
def twoSectionToRatFunc (u v : ℤ) (hv : v ≠ 0) :
    TwoSectionCoordinateRing u v →+* RatFunc ℚ :=
  IsLocalization.Away.lift (g := integerPolynomialToRatFunc) (boundaryPolynomial u v)
    (isUnit_iff_ne_zero.mpr (by
      intro hzero
      apply signedBoundary_ne_square u v 1 one_ne_zero hv 0
      simpa only [C_1, one_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hzero))

/-- The map from the localization extends the original polynomial inclusion. -/
theorem twoSectionToRatFunc_algebraMap (u v : ℤ) (hv : v ≠ 0) (p : ℤ[X]) :
    twoSectionToRatFunc u v hv (algebraMap ℤ[X] (TwoSectionCoordinateRing u v) p) =
      integerPolynomialToRatFunc p :=
  IsLocalization.Away.lift_eq (boundaryPolynomial u v) _ p

/-- The actual quadratic polynomial of Proposition 2.5 is irreducible over
its affine coordinate ring. The divisibility hypotheses produce its integral
coefficients and the discriminant identity. -/
theorem quadraticCoverPolynomial_irreducible (u v ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hεu : (4 : ℤ) ∣ 1 + ε * u)
    (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0) :
    Irreducible (quadraticPolynomial
      (algebraMap ℤ[X] (TwoSectionCoordinateRing u v) (quadraticConstantTerm u v ε))) := by
  let R : Type := TwoSectionCoordinateRing u v
  let : IsDomain R := Localization.Away.isDomain (boundaryPolynomial_ne_zero u v hv0)
  let c : ℤ[X] := quadraticConstantTerm u v ε
  let cR : R := algebraMap ℤ[X] R c
  let φ : R →+* RatFunc ℚ := twoSectionToRatFunc u v hv0
  have hdegree : (quadraticPolynomial cR).natDegree = 2 := by
    simpa only [quadraticPolynomial, C_1, one_mul] using
      (natDegree_quadratic (a := (1 : R)) (b := (1 : R)) (c := cR) one_ne_zero)
  apply ((quadraticPolynomial_monic cR).irreducible_iff_roots_eq_zero_of_degree_le_three
    hdegree.ge (hdegree.le.trans (by decide : (2 : ℕ) ≤ 3))).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have hxzero : x ^ 2 + x + cR = 0 := by
    simpa only [IsRoot.def, quadraticPolynomial, eval_add, eval_pow, eval_X, eval_C] using
      (isRoot_of_mem_roots hx)
  have hroot : (φ x) ^ 2 + φ x + φ cR = 0 := by
    have h := congrArg φ hxzero
    simpa only [map_add, map_pow, map_zero] using h
  have hdisc : 1 - 4 * φ cR =
      integerPolynomialToRatFunc (C ε * boundaryPolynomial u v) := by
    have h := congrArg integerPolynomialToRatFunc
      (quadraticConstantTerm_discriminant u v ε hεu hv)
    change 1 - 4 * twoSectionToRatFunc u v hv0 (algebraMap ℤ[X] R c) = _
    rw [twoSectionToRatFunc_algebraMap]
    simpa only [map_sub, map_one, map_mul, map_ofNat] using h
  have hε0 : ε ≠ 0 := by
    rcases hε with rfl | rfl <;> norm_num
  apply signedBoundary_ne_square u v ε hε0 hv0 (2 * φ x + 1)
  calc
    integerPolynomialToRatFunc (C ε * boundaryPolynomial u v) = 1 - 4 * φ cR :=
      hdisc.symm
    _ = (2 * φ x + 1) ^ 2 - 4 * ((φ x) ^ 2 + φ x + φ cR) := by ring
    _ = (2 * φ x + 1) ^ 2 := by rw [hroot, mul_zero, sub_zero]

/-- The quadratic covering algebra on the complement of the two sections. -/
abbrev TwoSectionQuadraticAlgebra (u v ε : ℤ) : Type :=
  AdjoinRoot (quadraticPolynomial
    (algebraMap ℤ[X] (TwoSectionCoordinateRing u v) (quadraticConstantTerm u v ε)))

/-- The explicit quadratic covering algebra is an integral domain. -/
theorem twoSectionQuadraticAlgebra_isDomain (u v ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hεu : (4 : ℤ) ∣ 1 + ε * u)
    (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0) :
    IsDomain (TwoSectionQuadraticAlgebra u v ε) := by
  let : IsDomain (TwoSectionCoordinateRing u v) :=
    Localization.Away.isDomain (boundaryPolynomial_ne_zero u v hv0)
  exact AdjoinRoot.isDomain_of_prime
    (quadraticCoverPolynomial_irreducible u v ε hε hεu hv hv0).prime

end ShimizuYamaguchi26BranchedCoverings

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.DyadicCollision
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.FormallyEtale
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The integral quadratic algebra in Proposition 2.5

For an odd integer `u` and an integer `v` divisible by four, the proof constructs
an integral polynomial `c(t)` and a sign `ε` with
`1 - 4 * c(t) = ε * (v * t - u)`. Thus adjoining a root of `X² + X + c(t)`
over `ℤ[t, 1 / (v * t - u)]` gives an actual finite free etale algebra.
For nonzero `v`, its rank is two.

The proof derives invertibility of the derivative from the equation of its
adjoined root, then uses the existing etale criterion. Connectedness of this
cover and its comparison with the complement of two projective-line sections
are not asserted here.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Proposition 2.5.
-/

noncomputable section

open Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- The monic quadratic equation used in the dyadic construction. -/
def quadraticPolynomial {R : Type*} [CommRing R] (c : R) : R[X] := X ^ 2 + X + C c

/-- The quadratic equation is monic over any commutative coefficient ring. -/
theorem quadraticPolynomial_monic {R : Type*} [CommRing R] (c : R) :
    (quadraticPolynomial c).Monic := by
  apply Monic.def.mpr
  by_cases h : (1 : R) = 0
  · exact eq_of_zero_eq_one h.symm (quadraticPolynomial c).leadingCoeff 1
  · simpa only [quadraticPolynomial, C_1, one_mul] using
      (leadingCoeff_quadratic (a := (1 : R)) (b := (1 : R)) (c := c) h)

/-- The derivative square is exactly the image of the quadratic discriminant. -/
theorem quadraticPolynomial_derivative_square {R : Type*} [CommRing R] (c : R) :
    (aeval (AdjoinRoot.root (quadraticPolynomial c))
      (quadraticPolynomial c).derivative) ^ 2 =
        algebraMap R (AdjoinRoot (quadraticPolynomial c)) (1 - 4 * c) := by
  let r : AdjoinRoot (quadraticPolynomial c) := AdjoinRoot.root (quadraticPolynomial c)
  have hpoly : quadraticPolynomial c = (X ^ 2 + X + C c : R[X]) := rfl
  have hroot : r ^ 2 + r + algebraMap R (AdjoinRoot (quadraticPolynomial c)) c = 0 := by
    have h : aeval r (quadraticPolynomial c) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have heval : aeval r (quadraticPolynomial c) =
        r ^ 2 + r + algebraMap R (AdjoinRoot (quadraticPolynomial c)) c := by
      calc
        aeval r (quadraticPolynomial c) = aeval r (X ^ 2 + X + C c : R[X]) :=
          congrArg (fun q : R[X] => aeval r q) hpoly
        _ = r ^ 2 + r + algebraMap R (AdjoinRoot (quadraticPolynomial c)) c := by
          rw [aeval_add, aeval_add, aeval_X_pow, aeval_X, aeval_C]
    exact heval.symm.trans h
  have hderivativePoly : (quadraticPolynomial c).derivative = C (2 : R) * X + 1 := by
    rw [hpoly, derivative_add, derivative_add, derivative_X_sq, derivative_X,
      derivative_C, add_zero]
  have hderivative : aeval r (quadraticPolynomial c).derivative = 2 * r + 1 := by
    calc
      aeval r (quadraticPolynomial c).derivative = aeval r (C (2 : R) * X + 1 : R[X]) :=
        congrArg (fun q : R[X] => aeval r q) hderivativePoly
      _ = 2 * r + 1 := by
        rw [aeval_add, aeval_mul, aeval_C, aeval_X, aeval_one, map_ofNat]
  change (aeval r (quadraticPolynomial c).derivative) ^ 2 = _
  rw [hderivative]
  calc
    (2 * r + 1) ^ 2 =
        4 * (r ^ 2 + r + algebraMap R (AdjoinRoot (quadraticPolynomial c)) c) +
          (1 - 4 * algebraMap R (AdjoinRoot (quadraticPolynomial c)) c) := by ring
    _ = algebraMap R (AdjoinRoot (quadraticPolynomial c)) (1 - 4 * c) := by
      rw [hroot, mul_zero, zero_add, map_sub, map_one, map_mul, map_ofNat]

/-- Invertibility of the discriminant makes the quadratic algebra etale.
The derivative condition is proved from the actual adjoined-root equation. -/
theorem quadraticPolynomial_etale {R : Type*} [CommRing R] (c : R)
    (hdisc : IsUnit (1 - 4 * c)) :
    Algebra.Etale R (AdjoinRoot (quadraticPolynomial c)) := by
  have hunit : IsUnit
      (aeval (AdjoinRoot.root (quadraticPolynomial c))
        (quadraticPolynomial c).derivative) := by
    apply (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [quadraticPolynomial_derivative_square]
    exact hdisc.map (algebraMap R (AdjoinRoot (quadraticPolynomial c)))
  have hformal : Algebra.FormallyEtale R (AdjoinRoot (quadraticPolynomial c)) :=
    EtaleFundamentalGroups.Kummer.formallyEtale_adjoinRoot_of_monic_of_isUnit_aeval_derivative
      (quadraticPolynomial_monic c) hunit
  exact { formallyEtale := hformal }

/-- The underlying free quadratic algebra has rank two over a nonzero ring. -/
theorem quadraticPolynomial_finrank {R : Type*} [CommRing R] [Nontrivial R] (c : R) :
    Module.finrank R (AdjoinRoot (quadraticPolynomial c)) = 2 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' (quadraticPolynomial_monic c)).basis,
    Fintype.card_fin, AdjoinRoot.powerBasis'_dim]
  simpa only [quadraticPolynomial, C_1, one_mul] using
    (natDegree_quadratic (a := (1 : R)) (b := (1 : R)) (c := c) one_ne_zero)

/-- The equation removed from the affine chart of the two-section complement. -/
def boundaryPolynomial (u v : ℤ) : ℤ[X] := C v * X - C u

/-- The integral constant term in the quadratic covering equation. -/
def quadraticConstantTerm (u v ε : ℤ) : ℤ[X] :=
  C ((1 + ε * u) / 4) - C (ε * (v / 4)) * X

/-- The explicit integral constant term has the required discriminant identity. -/
theorem quadraticConstantTerm_discriminant (u v ε : ℤ)
    (hu : (4 : ℤ) ∣ 1 + ε * u) (hv : (4 : ℤ) ∣ v) :
    1 - 4 * quadraticConstantTerm u v ε = C ε * boundaryPolynomial u v := by
  have hconst : 4 * ((1 + ε * u) / 4) = 1 + ε * u := Int.mul_ediv_cancel' hu
  have hlinear : 4 * (v / 4) = v := Int.mul_ediv_cancel' hv
  have hfour : (4 : ℤ[X]) * quadraticConstantTerm u v ε =
      C (4 * ((1 + ε * u) / 4)) - C ε * C (4 * (v / 4)) * X := by
    simp only [quadraticConstantTerm, map_mul, map_ofNat]
    ring
  rw [hfour, hconst, hlinear]
  simp only [boundaryPolynomial, map_add, map_mul, map_one]
  ring

/-- The affine coordinate ring obtained by removing `v * t - u = 0`. -/
abbrev TwoSectionCoordinateRing (u v : ℤ) : Type := Localization.Away (boundaryPolynomial u v)

/-- The actual discriminant is a unit after removing the boundary equation.
This uses the constructed integral constant term and either integral sign. -/
theorem quadraticConstantTerm_discriminant_isUnit (u v ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hεu : (4 : ℤ) ∣ 1 + ε * u)
    (hv : (4 : ℤ) ∣ v) :
    IsUnit (1 - 4 * algebraMap ℤ[X] (TwoSectionCoordinateRing u v)
      (quadraticConstantTerm u v ε)) := by
  have hsign : IsUnit (C ε : ℤ[X]) := by
    rcases hε with rfl | rfl
    · rw [map_one]
      exact isUnit_one
    · rw [map_neg, map_one]
      exact isUnit_one.neg
  have hdisc := congrArg (algebraMap ℤ[X] (TwoSectionCoordinateRing u v))
    (quadraticConstantTerm_discriminant u v ε hεu hv)
  simp only [map_sub, map_one, map_mul, map_ofNat] at hdisc
  rw [hdisc]
  exact (hsign.map (algebraMap ℤ[X] (TwoSectionCoordinateRing u v))).mul
    (IsLocalization.Away.algebraMap_isUnit (boundaryPolynomial u v))

/-- A nonzero denominator makes the boundary equation a nonzero polynomial. -/
theorem boundaryPolynomial_ne_zero (u v : ℤ) (hv : v ≠ 0) :
    boundaryPolynomial u v ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun f : ℤ[X] => f.coeff 1) h
  simp only [boundaryPolynomial, coeff_sub, coeff_C_mul_X, coeff_C,
    Nat.one_ne_zero, ite_false, sub_zero, coeff_zero] at hcoeff
  exact hv hcoeff

/-- The algebraic construction in Proposition 2.5: over the stated affine
localization there is a finite free etale quadratic algebra of rank two. -/
theorem exists_finite_etale_quadratic_algebra (u v : ℤ)
    (hu : Odd u) (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0) :
    ∃ (ε : ℤ) (c : ℤ[X]), (ε = 1 ∨ ε = -1) ∧
      1 - 4 * c = C ε * boundaryPolynomial u v ∧
      let R : Type := TwoSectionCoordinateRing u v
      let f : R[X] := quadraticPolynomial (algebraMap ℤ[X] R c)
      Algebra.Etale R (AdjoinRoot f) ∧ Module.Finite R (AdjoinRoot f) ∧
        Module.Free R (AdjoinRoot f) ∧ Module.finrank R (AdjoinRoot f) = 2 := by
  obtain ⟨ε, hε, hεu⟩ := exists_sign_four_dvd_one_add u hu
  let c : ℤ[X] := quadraticConstantTerm u v ε
  have hdisc : 1 - 4 * c = C ε * boundaryPolynomial u v :=
    quadraticConstantTerm_discriminant u v ε hεu hv
  refine ⟨ε, c, hε, hdisc, ?_⟩
  let R : Type := TwoSectionCoordinateRing u v
  let : IsDomain R := Localization.Away.isDomain (boundaryPolynomial_ne_zero u v hv0)
  let cR : R := algebraMap ℤ[X] R c
  have hunit : IsUnit (1 - 4 * cR) :=
    quadraticConstantTerm_discriminant_isUnit u v ε hε hεu hv
  exact ⟨quadraticPolynomial_etale cR hunit,
    (quadraticPolynomial_monic cR).finite_adjoinRoot,
    (quadraticPolynomial_monic cR).free_adjoinRoot,
    quadraticPolynomial_finrank cR⟩

end ShimizuYamaguchi26BranchedCoverings

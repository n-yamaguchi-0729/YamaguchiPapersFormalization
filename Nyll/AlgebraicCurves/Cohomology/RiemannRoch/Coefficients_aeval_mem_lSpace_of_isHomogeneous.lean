/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Mul_mem_lSpace_add
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Pole bounds for the coefficients of a homogeneous substitution

This is the pole-control step of the Riemann--Roch proof of Tsen's theorem
(Stacks Project, Tag 03RD). Multiplication is supplied by the existing divisor theory.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

private theorem mul_coefficients_mem_lSpace
    {K F τ : Type*} [Field K] [Field F] [Algebra K F]
    {D E : Divisor K F} {p q : MvPolynomial τ F}
    (hp : p ∈ MvPolynomial.coeffsIn τ (LSpace D))
    (hq : q ∈ MvPolynomial.coeffsIn τ (LSpace E)) :
    p * q ∈ MvPolynomial.coeffsIn τ (LSpace (D + E)) := by
  have h : p * q ∈ MvPolynomial.coeffsIn τ (LSpace D * LSpace E) := by
    rw [MvPolynomial.coeffsIn_mul]
    exact Submodule.mul_mem_mul hp hq
  have hle : LSpace D * LSpace E ≤ LSpace (D + E) :=
    Submodule.mul_le.mpr fun _ ha _ hb => mul_mem_lSpace_add ha hb
  intro a
  exact hle (h a)

private theorem pow_coefficients_mem_lSpace
    {K F τ : Type*} [Field K] [Field F] [Algebra K F]
    {D : Divisor K F} {p : MvPolynomial τ F}
    (hp : p ∈ MvPolynomial.coeffsIn τ (LSpace D)) (n : ℕ) :
    p ^ n ∈ MvPolynomial.coeffsIn τ (LSpace (n • D)) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_nsmul]
    exact MvPolynomial.one_coeffsIn.mpr one_mem_lSpace_zero
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_coefficients_mem_lSpace ih hp

/-- Substitution of polynomials with coefficients in L(D) into a degree-d homogeneous
form with coefficients in L(E) has all coefficients in L(E + dD). -/
theorem coefficients_aeval_mem_lSpace_of_isHomogeneous
    {K F σ τ : Type*} [Field K] [Field F] [Algebra K F]
    {d : ℕ} (p : MvPolynomial σ F) (q : σ → MvPolynomial τ F)
    (D E : Divisor K F) (hhom : p.IsHomogeneous d)
    (hp : ∀ a : σ →₀ ℕ, p.coeff a ∈ LSpace E)
    (hq : ∀ i : σ, ∀ a : τ →₀ ℕ, (q i).coeff a ∈ LSpace D) :
    ∀ a : τ →₀ ℕ, (MvPolynomial.aeval q p).coeff a ∈ LSpace (E + d • D) := by
  classical
  have hpoly : MvPolynomial.aeval q p ∈
      MvPolynomial.coeffsIn τ (LSpace (E + d • D)) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    apply (MvPolynomial.coeffsIn τ (LSpace (E + d • D))).sum_mem
    intro a ha
    have hprod (s : Finset σ) :
        (∏ i ∈ s, q i ^ a i) ∈
          MvPolynomial.coeffsIn τ (LSpace ((∑ i ∈ s, a i) • D)) := by
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.prod_empty, Finset.sum_empty, zero_nsmul]
        exact MvPolynomial.one_coeffsIn.mpr one_mem_lSpace_zero
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, add_nsmul]
        exact mul_coefficients_mem_lSpace (pow_coefficients_mem_lSpace (hq i) (a i)) ih
    have hmon := hprod a.support
    rw [← hhom.degree_eq_sum_deg_support ha] at hmon
    exact mul_coefficients_mem_lSpace (MvPolynomial.C_mem_coeffsIn.mpr (hp a)) hmon
  exact hpoly

end AlgebraicCurve

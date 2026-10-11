/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LaurentPolynomial_isUnit_iff_exists_C_mul_T.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Laurent Polynomial is Unit iff exists C mul T
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Polynomial.Proofs.LaurentPolynomial_isUnit_iff_exists_C_mul_T

open LaurentPolynomial

universe u

theorem _root_.LaurentPolynomial.isUnit_iff_exists_C_mul_T
    {R : Type u} [CommRing R] [IsDomain R] (f : R[T;T⁻¹]) :
    IsUnit f ↔ ∃ (c : Rˣ) (n : ℤ), f = C (c : R) * T n := by
  constructor
  · intro hf
    obtain ⟨u, rfl⟩ := hf
    obtain ⟨a, p, hp⟩ := LaurentPolynomial.exists_T_pow (u : R[T;T⁻¹])
    obtain ⟨b, q, hq⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹ : R[T;T⁻¹])
    have hpq : p * q = Polynomial.X ^ (a + b) := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow, mul_mul_mul_comm, Units.mul_inv, one_mul,
        ← T_add, Nat.cast_add]
    have hdvd : p ∣ Polynomial.X ^ (a + b) := ⟨q, hpq.symm⟩
    obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X _).1 hdvd
    obtain ⟨v, hv⟩ := hassoc.symm
    obtain ⟨c, hc, hcv⟩ := Polynomial.isUnit_iff.1 v.isUnit
    obtain ⟨c, rfl⟩ := hc
    refine ⟨c, (i : ℤ) - a, ?_⟩
    have hu : (u : R[T;T⁻¹]) = Polynomial.toLaurent p * T (-(a : ℤ)) := by
      rw [hp, mul_T_assoc, add_neg_cancel, T_zero, mul_one]
    rw [hu, ← hv, ← hcv, mul_comm (Polynomial.X ^ i), map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X_pow,
      mul_assoc, ← T_add, sub_eq_add_neg]
  · rintro ⟨c, n, rfl⟩
    exact ((Units.isUnit c).map C).mul (isUnit_T n)
end AlgebraicCurves.Foundations.Polynomial.Proofs.LaurentPolynomial_isUnit_iff_exists_C_mul_T
end ProofImplementation

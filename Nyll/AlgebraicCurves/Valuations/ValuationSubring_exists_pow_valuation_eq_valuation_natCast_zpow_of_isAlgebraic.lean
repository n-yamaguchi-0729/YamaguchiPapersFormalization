/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Conv
import Nyll.AlgebraicCurves.Valuations.ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic

/-!
# Valuation Subring exists pow valuation eq valuation nat Cast zpow of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic


namespace P2mR1W0zpow

section ValueGroup

variable {K : Type*} [Field K] (A : ValuationSubring K)

theorem valuation_intCast_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    A.valuation (a : K) = 1 := by
  have hcop : IsCoprime a (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right a p
    have h2 : (Int.gcd a p : ℤ) ∣ (p : ℤ) := Int.gcd_dvd_right a p
    have h3 : Int.gcd a p ∣ p := by exact_mod_cast h2
    rcases (Nat.dvd_prime hp).mp h3 with h | h
    · exact h
    · exfalso
      apply ha
      have h4 : (Int.gcd a p : ℤ) ∣ a := Int.gcd_dvd_left a p
      rw [h] at h4
      exact h4
  obtain ⟨s, t, hst⟩ := hcop
  have hle : A.valuation (a : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  have h1 : (s : K) * (a : K) + (t : K) * (p : K) = 1 := by
    have := congrArg (fun z : ℤ => (z : K)) hst
    push_cast at this
    exact this
  have hs : A.valuation (s : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A s)
  have ht : A.valuation (t : K) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A t)
  have hlt1 : A.valuation ((s : K) * (a : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (s : K) * A.valuation (a : K) ≤ 1 * A.valuation (a : K) :=
          mul_le_mul_left hs _
      _ < 1 := by rw [one_mul]; exact hlt
  have hlt2 : A.valuation ((t : K) * (p : K)) < 1 := by
    rw [map_mul]
    calc A.valuation (t : K) * A.valuation (p : K) ≤ 1 * A.valuation (p : K) :=
          mul_le_mul_left ht _
      _ < 1 := by rw [one_mul]; exact hAp
  have := A.valuation.map_add_lt hlt1 hlt2
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem exists_valuation_natCast_eq_pow {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, A.valuation (n : K) = A.valuation (p : K) ^ e := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  refine ⟨e, ?_⟩
  have h1 : A.valuation ((n' : ℤ) : K) = 1 :=
    valuation_intCast_eq_one_of_not_dvd A hp hAp (by exact_mod_cast hn')
  push_cast
  rw [map_mul, map_pow]
  rw [Int.cast_natCast] at h1
  rw [h1, mul_one]

theorem exists_valuation_ratCast_eq_zpow [CharZero K] {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {c : ℚ} (hc : c ≠ 0) :
    ∃ k : ℤ, A.valuation (c : K) = A.valuation (p : K) ^ k := by
  have hp0 : A.valuation (p : K) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]; exact_mod_cast hp.ne_zero
  have hnum : c.num ≠ 0 := Rat.num_ne_zero.mpr hc
  obtain ⟨e₁, he₁⟩ := exists_valuation_natCast_eq_pow A hp hAp (Int.natAbs_ne_zero.mpr hnum)
  obtain ⟨e₂, he₂⟩ := exists_valuation_natCast_eq_pow A hp hAp c.den_nz
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  have hnumv : A.valuation (c.num : K) = A.valuation (p : K) ^ e₁ := by
    rw [← he₁]
    rcases Int.natAbs_eq c.num with h | h
    · conv_lhs => rw [h]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
  rw [Rat.cast_def, map_div₀, hnumv, he₂, zpow_sub₀ hp0, zpow_natCast, zpow_natCast]

variable [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

theorem exists_pow_valuation_eq_valuation_prime_zpow {p : ℕ} (hp : p.Prime)
    (hAp : A.valuation (p : K) < 1) {x : K} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ, A.valuation x ^ n = A.valuation (p : K) ^ k := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  obtain ⟨n, hn, c, hc, hcv⟩ :=
    ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic (E := ℚ) A hx
  obtain ⟨k, hk⟩ := exists_valuation_ratCast_eq_zpow A hp hAp hc
  refine ⟨n, hn, k, ?_⟩
  rw [← map_pow, hcv, ← hk, eq_ratCast]

end ValueGroup

end P2mR1W0zpow

theorem _root_.ValuationSubring.exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1)
    {x : K} (hx : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ, A.valuation x ^ n = A.valuation (p : K) ^ k :=
  P2mR1W0zpow.exists_pow_valuation_eq_valuation_prime_zpow A hp hAp hx
end ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation

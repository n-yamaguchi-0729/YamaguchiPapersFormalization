/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Eisenstein irreducibility for an explicit Kummer polynomial

For a prime element `t`, the polynomial `X ^ n - t` is Eisenstein at `(t)`.
If the original domain is integrally closed, Gauss's lemma then transports
this irreducibility to its fraction field.  This is the field shared by the
original domain and its boundary localization, where the Kummer cover is
etale.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v

/-- A prime element does not belong to the square of its principal ideal. -/
theorem prime_notMem_span_singleton_sq
    {R : Type u} [CommRing R] [IsDomain R] {t : R} (ht : Prime t) :
    t ∉ (Ideal.span ({t} : Set R)) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro h
  obtain ⟨a, ha⟩ := h
  apply ht.not_isUnit
  rw [isUnit_iff_dvd_one]
  refine ⟨a, ?_⟩
  apply mul_left_cancel₀ ht.ne_zero
  simpa [pow_two, mul_assoc] using ha

/-- `X ^ n - t` is Eisenstein at `(t)` when `t` is prime and `n` is positive. -/
theorem isEisensteinAt_X_pow_sub_C_of_prime
    {R : Type u} [CommRing R] [IsDomain R] {t : R} (ht : Prime t)
    {n : ℕ} (hn : 0 < n) :
    (X ^ n - C t).IsEisensteinAt (Ideal.span ({t} : Set R)) := by
  refine (monic_X_pow_sub_C t hn.ne').isEisensteinAt_of_mem_of_notMem
    (Ideal.isPrime_span_singleton_of_prime ht).ne_top ?_ ?_
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    rw [Ideal.mem_span_singleton]
    by_cases hi₀ : i = 0
    · subst i
      simp [Polynomial.coeff_X_pow, hn.ne'.symm]
    · have hin : i ≠ n := Nat.ne_of_lt hi
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, hi₀, hin]
  · simpa [Polynomial.coeff_X_pow, hn.ne'.symm, Ideal.neg_mem_iff] using
      prime_notMem_span_singleton_sq ht

/-- `X ^ n - t` is irreducible when `t` is prime and `n` is positive. -/
theorem irreducible_X_pow_sub_C_of_prime
    {R : Type u} [CommRing R] [IsDomain R] {t : R} (ht : Prime t)
    {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C t) :=
  (isEisensteinAt_X_pow_sub_C_of_prime ht hn).irreducible
    (Ideal.isPrime_span_singleton_of_prime ht)
    (monic_X_pow_sub_C t hn.ne').isPrimitive
    (by simpa using hn)

/--
The explicit Kummer polynomial remains irreducible over any chosen fraction
field of an integrally closed original domain.  The only coefficient map in
the statement is the canonical `algebraMap R K`.
-/
theorem irreducible_X_pow_sub_C_fractionRing_of_prime
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {t : R} (ht : Prime t)
    {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C (algebraMap R K t)) := by
  have hmap :
      Irreducible ((X ^ n - C t).map (algebraMap R K)) :=
    (monic_X_pow_sub_C t hn.ne').irreducible_iff_irreducible_map_fraction_map.mp
      (irreducible_X_pow_sub_C_of_prime ht hn)
  simpa using hmap

/--
After inverting the boundary parameter, the same Kummer polynomial remains
irreducible.  The proof uses the single canonical map from the localization
to the chosen fraction field; it does not introduce an algebra tower.
-/
theorem irreducible_X_pow_sub_C_away_of_prime
    {R : Type u} {S : Type v} {K : Type*}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] {t : R} [IsLocalization.Away t S]
    [Field K] [Algebra R K] [IsFractionRing R K] (ht : Prime t)
    {n : ℕ} (hn : 0 < n) :
    Irreducible (X ^ n - C (algebraMap R S t)) := by
  let : IsDomain S := IsLocalization.Away.isDomain S ht.ne_zero
  have hpow : Submonoid.powers t ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero)
  let ι : S →+* K :=
    (Localization.mapToFractionRing K (Submonoid.powers t) S hpow).toRingHom
  have hι_injective : Function.Injective ι := by
    dsimp only [ι, Localization.mapToFractionRing]
    refine (IsLocalization.lift_injective_iff _).2 fun a b ↦ ?_
    exact ⟨fun h ↦ congrArg _ (IsLocalization.injective S hpow h),
      fun h ↦ congrArg _ (IsFractionRing.injective R K h)⟩
  have hι_comm (a : R) : ι (algebraMap R S a) = algebraMap R K a := by
    change
      (Localization.mapToFractionRing K (Submonoid.powers t) S hpow)
          (algebraMap R S a) = algebraMap R K a
    exact (Localization.mapToFractionRing K (Submonoid.powers t) S hpow).commutes a
  have hprimitive :
      (X ^ n - C (algebraMap R S t)).IsPrimitive :=
    (monic_X_pow_sub_C (algebraMap R S t) hn.ne').isPrimitive
  refine hprimitive.irreducible_of_irreducible_map_of_injective hι_injective ?_
  simpa [hι_comm] using irreducible_X_pow_sub_C_fractionRing_of_prime ht hn

end EtaleFundamentalGroups.Kummer

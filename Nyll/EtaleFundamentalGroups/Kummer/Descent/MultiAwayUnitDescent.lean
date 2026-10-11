/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Descent.Unit

/-!
# Unit descent from a multi-boundary complement

This file extends unit descent from one prime boundary parameter to a finite
product of prime parameters.  A divisor of a power of the boundary product
which is divisible by none of its prime factors must be a unit.
-/

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe u v w

/-- Strip a finite product of prime factors from the right side of a
divisibility relation when none of those factors divides the left side. -/
private theorem dvd_left_of_dvd_mul_finsetProduct_of_primes_of_not_dvd
    {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type w} (s : Finset ι) (t : ι → R) {a b : R}
    (ht : ∀ i ∈ s, Prime (t i))
    (hta : ∀ i ∈ s, ¬ t i ∣ a)
    (h : a ∣ b * ∏ i ∈ s, t i) :
    a ∣ b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using h
  | @insert i s hi ih =>
      apply ih
      · intro j hj
        exact ht j (Finset.mem_insert_of_mem hj)
      · intro j hj
        exact hta j (Finset.mem_insert_of_mem hj)
      · exact
          ((ht i (Finset.mem_insert_self i s)).left_dvd_or_dvd_right_of_dvd_mul
            (by
              simpa [Finset.prod_insert hi, mul_assoc, mul_comm, mul_left_comm]
                using h)).resolve_left
            (hta i (Finset.mem_insert_self i s))

/--
Let `S` be obtained by inverting a finite product of prime elements.  An
element divisible by none of those primes was already a unit if its image is
a unit in `S`.
-/
theorem isUnit_of_isUnit_algebraMap_away_finsetProduct_of_primes_of_not_dvd
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    {a : R} (ht : ∀ i ∈ s, Prime (t i))
    (hta : ∀ i ∈ s, ¬ t i ∣ a)
    (ha : IsUnit (algebraMap R S a)) :
    IsUnit a := by
  obtain ⟨m, ham⟩ :=
    (IsLocalization.Away.algebraMap_isUnit_iff (∏ i ∈ s, t i)).mp ha
  induction m with
  | zero =>
      exact isUnit_of_dvd_one (by simpa using ham)
  | succ m ih =>
      apply ih
      exact
        dvd_left_of_dvd_mul_finsetProduct_of_primes_of_not_dvd
          s t ht hta (b := (∏ i ∈ s, t i) ^ m) (by
            simpa [pow_succ] using ham)

/--
For a positive natural number, characteristic zero on every boundary
component supplies all nondivisibility inputs needed by multi-boundary unit
descent.
-/
theorem isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    (ht : ∀ i ∈ s, Prime (t i))
    (hCharZero : ∀ i ∈ s, CharZero (R ⧸ Ideal.span {t i}))
    {n : ℕ} (hn : 0 < n)
    (hnS : IsUnit (algebraMap R S (n : R))) :
    IsUnit (n : R) := by
  apply
    isUnit_of_isUnit_algebraMap_away_finsetProduct_of_primes_of_not_dvd
      (R := R) (S := S) s t ht
  · intro i hi
    let : CharZero (R ⧸ Ideal.span {t i}) := hCharZero i hi
    exact not_dvd_natCast_of_charZero_quotient n hn
  · exact hnS

end EtaleFundamentalGroups.Kummer

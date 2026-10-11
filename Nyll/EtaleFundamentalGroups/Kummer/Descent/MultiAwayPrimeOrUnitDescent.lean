/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Descent.MultiAwayUnitDescent

/-!
# Unit descent with inactive boundary units

After localizing a strict-normal-crossings chart at a prime, every boundary
parameter is either still prime or has become a unit.  This file extends the
multi-away unit descent theorem to precisely that situation, without
reindexing the surviving boundary components.
-/

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe u v w

/-- Remove a finite family of prime-or-unit factors from the right side of a
divisibility relation.  Nondivisibility is required only for the prime
factors; unit factors cancel directly. -/
private theorem dvd_left_of_dvd_mul_finsetProduct_of_prime_or_unit
    {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type w} (s : Finset ι) (t : ι → R) {a b : R}
    (ht : ∀ i ∈ s, Prime (t i) ∨ IsUnit (t i))
    (hta : ∀ i ∈ s, Prime (t i) → ¬ t i ∣ a)
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
      · intro j hj hjPrime
        exact hta j (Finset.mem_insert_of_mem hj) hjPrime
      · have h' : a ∣ (b * ∏ j ∈ s, t j) * t i := by
          simpa [Finset.prod_insert hi, mul_assoc, mul_comm, mul_left_comm]
            using h
        rcases ht i (Finset.mem_insert_self i s) with hiPrime | hiUnit
        · exact
            (hiPrime.left_dvd_or_dvd_right_of_dvd_mul (by
              simpa [mul_comm] using h')).resolve_left
              (hta i (Finset.mem_insert_self i s) hiPrime)
        · exact hiUnit.dvd_mul_right.mp h'

/--
Let `S` be obtained by inverting a product whose factors are each prime or a
unit.  If `a` is divisible by none of the prime factors and becomes a unit
in `S`, then it was already a unit.
-/
theorem isUnit_of_isUnit_algebraMap_away_finsetProduct_of_prime_or_unit
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    {a : R} (ht : ∀ i ∈ s, Prime (t i) ∨ IsUnit (t i))
    (hta : ∀ i ∈ s, Prime (t i) → ¬ t i ∣ a)
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
        dvd_left_of_dvd_mul_finsetProduct_of_prime_or_unit
          s t ht hta (b := (∏ i ∈ s, t i) ^ m) (by
            simpa [pow_succ] using ham)

/--
Characteristic zero along every surviving prime component supplies the
nondivisibility needed to descend a positive natural-number unit.  Boundary
components which became units after localization require no residue
characteristic hypothesis.
-/
theorem isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct_of_prime_or_unit
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    (ht : ∀ i ∈ s, Prime (t i) ∨ IsUnit (t i))
    (hCharZero : ∀ i ∈ s, Prime (t i) →
      CharZero (R ⧸ Ideal.span {t i}))
    {n : ℕ} (hn : 0 < n)
    (hnS : IsUnit (algebraMap R S (n : R))) :
    IsUnit (n : R) := by
  apply
    isUnit_of_isUnit_algebraMap_away_finsetProduct_of_prime_or_unit
      (R := R) (S := S) s t ht
  · intro i hi hiPrime
    let : CharZero (R ⧸ Ideal.span {t i}) :=
      hCharZero i hi hiPrime
    exact not_dvd_natCast_of_charZero_quotient n hn
  · exact hnS

end EtaleFundamentalGroups.Kummer

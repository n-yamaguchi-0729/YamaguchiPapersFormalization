/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Invertible
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.PGroup

/-!
# Prime-to-characteristic divisors survive the wild quotient

The order of a finite p-group divides a power of p. Thus every divisor of
the inertia order coprime to p divides the index of wild inertia. This
converts the actual radical ramification divisibility into finite tame-order
divisibility once the finite inertia cardinality has been supplied.
-/

namespace EtaleFundamentalGroups.Inertia

universe u

/-- Invertibility of an actual residue-field integer makes it coprime to
that field's own exponential characteristic, including characteristic zero. -/
theorem natCast_isUnit_coprime_ringExpChar
    (k : Type u) [Field k] (n : ℕ) (hn : IsUnit (n : k)) :
    Nat.Coprime n (ringExpChar k) := by
  obtain hp | hone := expChar_is_prime_or_one k (ringExpChar k)
  · have : CharP k (ringExpChar k) := (expChar_prime_iff (R := k) hp).mp inferInstance
    exact (hp.coprime_iff_not_dvd.mpr ((CharP.isUnit_natCast_iff hp).mp hn)).symm
  · rw [hone]
    exact Nat.coprime_one_right n

/-- A divisor prime to p survives quotienting a finite group by any
p-subgroup. Normality is not needed for the index calculation. -/
theorem primeTo_dvd_quotient_card_of_dvd_card_of_isPGroup
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) (p n : ℕ) (hP : IsPGroup p P)
    (hn : Nat.Coprime n p) (hdiv : n ∣ Nat.card G) :
    n ∣ Nat.card (G ⧸ P) := by
  obtain ⟨r, hr⟩ := hP.exists_card_dvd_pow
  have hcoprime : Nat.Coprime n (Nat.card P) :=
    Nat.Coprime.of_dvd_right hr (hn.pow_right r)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P] at hdiv
  exact hcoprime.dvd_of_dvd_mul_right hdiv

end EtaleFundamentalGroups.Inertia

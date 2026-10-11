/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Normalization.Localization
import EtaleFundamentalGroups.Inertia.Localized.Cardinality
import EtaleFundamentalGroups.Inertia.Residue.Coprimality

/-!
# Coprimality of normalization inertia from a ramification-index unit

At a characteristic-zero height-one divisor, the cardinality of the
ideal-theoretic inertia subgroup equals the ramification index.  A unit
ramification index therefore remains prime to every prime residue
characteristic reached from that divisor.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL uk

/-- A ramification index that is invertible on a prime divisor forces the
normalization inertia group to have order prime to any prime characteristic
of a residue ring receiving that divisor's function field. -/
theorem normalizationInertia_coprime_of_ramificationIdx_isUnit
    {A : Type uA} {K : Type uK} {L : Type uL} {k : Type uk}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing k] [Nontrivial k]
    (t : A) (ht : Prime t)
    [CharZero (A ⧸ Ideal.span {t})]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {t})]
    (hunit : IsUnit
      ((Q.ramificationIdx A : ℕ) : A ⧸ Ideal.span {t}))
    (phi : (A ⧸ Ideal.span {t}) →+* k)
    (p : ℕ) [CharP k p] (hp : p.Prime) :
    Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  let P := Ideal.span {t}
  let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime ht
  have hPheight : P.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit
  have hcard : Nat.card (Q.toAddSubgroup.inertia Gal(L/K)) =
      Q.ramificationIdx A := by
    rw [normalizationInertia_eq_localizedNormalizationInertia
      (K := K) (L := L) P Q]
    exact localizedNormalizationInertia_card_eq_ramificationIdx
      (K := K) (L := L) P hPheight Q
  have hunit_k : IsUnit ((Q.ramificationIdx A : ℕ) : k) := by
    simpa only [map_natCast] using hunit.map phi
  rw [hcard]
  exact natCoprime_of_isUnit_natCast_of_charP
    p (Q.ramificationIdx A) hp hunit_k

end EtaleFundamentalGroups

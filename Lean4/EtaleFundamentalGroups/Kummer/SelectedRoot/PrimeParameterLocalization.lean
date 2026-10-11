/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.CharP.Algebra

/-!
# Prime boundary parameters after localization

A prime boundary parameter remains prime at every larger prime containing
it, and becomes a unit at every other prime localization.  In the first
case, characteristic zero of its generic residue ring is preserved by the
localization.  These are the exact inputs needed by prime-or-unit
multi-boundary unit descent.
-/

namespace EtaleFundamentalGroups.Kummer

universe u

/-- A prime element is either still prime or becomes a unit after
localization at a prime ideal. -/
theorem prime_or_isUnit_algebraMap_localizationAtPrime
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] {t : A} (ht : Prime t) :
    Prime (algebraMap A (Localization.AtPrime P) t) ∨
      IsUnit (algebraMap A (Localization.AtPrime P) t) := by
  by_cases htP : t ∈ P
  · left
    have htNe : algebraMap A (Localization.AtPrime P) t ≠ 0 := by
      intro htZero
      exact ht.ne_zero
        ((IsLocalization.injective (Localization.AtPrime P)
          P.primeCompl_le_nonZeroDivisors) (by
            simpa only [map_zero] using htZero))
    apply (Ideal.span_singleton_prime htNe).mp
    let : (Ideal.span ({t} : Set A)).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime ht
    have hmapPrime :
        ((Ideal.span ({t} : Set A)).map
          (algebraMap A (Localization.AtPrime P))).IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime P
        (P.span_singleton_le_iff_mem.mpr htP)
    simpa only [Ideal.map_span, Set.image_singleton] using hmapPrime
  · right
    exact
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime P) P t).mpr htP

/-- Characteristic zero along a prime divisor is preserved when localizing
at a larger prime containing that divisor. -/
theorem charZero_quotient_algebraMap_localizationAtPrime
    {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] {t : A} (ht : Prime t)
    (htP : t ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span {t})) :
    CharZero
      (Localization.AtPrime P ⧸
        Ideal.span {algebraMap A (Localization.AtPrime P) t}) := by
  let J : Ideal A := Ideal.span {t}
  let V := Localization.AtPrime P
  let I : Ideal V := J.map (algebraMap A V)
  let : J.IsPrime := Ideal.isPrime_span_singleton_of_prime ht
  have hJP : J ≤ P := by
    exact P.span_singleton_le_iff_mem.mpr htP
  have hunder : I.under A = J := by
    exact Ideal.under_map_of_isLocalizationAtPrime P hJP
  let : CharZero (A ⧸ I.under A) := by
    rw [hunder]
    exact hCharZero
  have htarget : CharZero (V ⧸ I) :=
    charZero_of_injective_algebraMap
      (Ideal.algebraMap_quotient_injective (R := A) (A := V) (I := I))
  have hI : I = Ideal.span {algebraMap A V t} := by
    simp [I, J, Ideal.map_span]
  rw [← hI]
  exact htarget

end EtaleFundamentalGroups.Kummer

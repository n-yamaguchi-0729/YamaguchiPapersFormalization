/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# Intersecting the height-one localizations of a UFD

An element of the fraction field of a unique factorization domain which lies
in the localization at every prime element already lies in the original
domain.  The proof uses a reduced numerator and denominator and detects every
nonunit denominator by one of its prime factors.

This is the codimension-one intersection input needed in the two-dimensional
local-purity argument.  It does not assume normality, reflexivity, or a purity
statement.
-/

noncomputable section

namespace EtaleFundamentalGroups

open nonZeroDivisors

universe u v

/-- A fraction over a UFD which belongs to the localization at every prime
element belongs to the image of the UFD itself. -/
theorem mem_bot_of_mem_localization_primeElement
    {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (z : K)
    (hz : ∀ (p : A) (hp : Prime p),
      letI : (Ideal.span {p}).IsPrime :=
        Ideal.isPrime_span_singleton_of_prime hp
      z ∈ Localization.subalgebra.ofField K (Ideal.span {p}).primeCompl
        (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))) :
    z ∈ (⊥ : Subalgebra A K) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A z
  obtain ⟨a', b', c, hrel, ha, hb'⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have hc : c ≠ 0 := by
    intro hc
    apply mem_nonZeroDivisors_iff_ne_zero.mp hb
    simpa [hc] using hb'.symm
  have hb'0 : b' ≠ 0 := by
    intro hb'0
    apply mem_nonZeroDivisors_iff_ne_zero.mp hb
    simpa [hb'0] using hb'.symm
  have hz_reduced : algebraMap A K a' / algebraMap A K b' = z := by
    rw [← hab, ← ha, ← hb']
    have hcK : algebraMap A K c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hc
    have hbK : algebraMap A K b' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb'0
    simp only [map_mul]
    apply (div_eq_div_iff hbK (mul_ne_zero hcK hbK)).2
    rw [← mul_assoc, mul_comm (algebraMap A K a') (algebraMap A K c)]
  have hb'_unit : IsUnit b' := by
    by_contra hb'_unit
    obtain ⟨p, hp, hpb'⟩ := WfDvdMonoid.exists_irreducible_factor hb'_unit hb'0
    have hp' : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp
    let : (Ideal.span {p}).IsPrime :=
      Ideal.isPrime_span_singleton_of_prime hp'
    have hzloc := hz p hp'
    change ∃ (d s : A) (_ : s ∈ (Ideal.span {p}).primeCompl),
      z = algebraMap A K d * (algebraMap A K s)⁻¹ at hzloc
    obtain ⟨d, s, hs, hds⟩ := hzloc
    have hs0 : s ≠ 0 := by
      intro hs0
      subst s
      exact hs (Ideal.zero_mem (Ideal.span {p}))
    have hcross : a' * s = d * b' := by
      apply IsFractionRing.injective A K
      rw [map_mul, map_mul]
      have hbK : algebraMap A K b' ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb'0
      have hsK : algebraMap A K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hs0
      rw [← div_eq_div_iff hbK hsK, hz_reduced, hds]
      simp [div_eq_mul_inv]
    have hp_as : p ∣ a' * s := hcross ▸ dvd_mul_of_dvd_right hpb' d
    rcases hp'.2.2 a' s hp_as with hpa' | hps
    · exact hp'.not_isUnit (hrel hpa' hpb')
    · exact hs (Ideal.mem_span_singleton.mpr hps)
  rw [Algebra.mem_bot]
  refine ⟨a' * ↑hb'_unit.unit⁻¹, ?_⟩
  simpa [div_eq_mul_inv] using hz_reduced

end EtaleFundamentalGroups

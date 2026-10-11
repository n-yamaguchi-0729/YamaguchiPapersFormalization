/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Killing a minimal prime in a domain localization

This file isolates the order-sensitive final step used for a retained
generic component.  A prime over the generic point of an integral base is a
minimal prime.  Its extension to a larger-prime localization is zero once
that localization has independently been shown to be a domain.

The domain hypothesis is deliberately imposed only on the localization; it
is not used to produce minimality of the original prime.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uA

/-- A prime of an integral algebra lying over the zero ideal of the base is
a minimal prime of the algebra. -/
theorem prime_liesOver_bot_mem_minimalPrimes
    {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    (N : Ideal A) [N.IsPrime] [N.LiesOver (⊥ : Ideal R)] :
    N ∈ minimalPrimes A := by
  have hmin :=
    Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) N
  have hUnder : N.under R = (⊥ : Ideal R) :=
    (N.over_def (⊥ : Ideal R)).symm
  rw [hUnder, Ideal.map_bot] at hmin
  exact hmin

/-- A minimal prime contained in `Q` maps to zero in the localization at
`Q`, provided that localization has already been proved to be a domain. -/
theorem minimalPrime_map_eq_bot_localizationAtPrime_of_isDomain
    {A : Type uA} [CommRing A]
    (N Q : Ideal A) [N.IsPrime] [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)]
    (hNMinimal : N ∈ minimalPrimes A) (hNQ : N ≤ Q) :
    N.map (algebraMap A (Localization.AtPrime Q)) = ⊥ := by
  have hNMapMinimal :
      N.map (algebraMap A (Localization.AtPrime Q)) ∈
        minimalPrimes (Localization.AtPrime Q) := by
    have hMappedMinimal :
        N.map (algebraMap A (Localization.AtPrime Q)) ∈
          ((⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime Q))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl
        (Localization.AtPrime Q) (⊥ : Ideal A)]
      change
        (N.map (algebraMap A (Localization.AtPrime Q))).under A ∈
          minimalPrimes A
      rw [Ideal.under_map_of_isLocalizationAtPrime Q hNQ]
      exact hNMinimal
    simpa only [Ideal.map_bot] using hMappedMinimal
  apply le_antisymm
  · exact hNMapMinimal.2 ⟨inferInstance, bot_le⟩ bot_le
  · exact bot_le

/-- Combined integral-generic-prime form: after domainhood of the
localization at a containing prime has been established, a prime lying over
the base generic point vanishes there. -/
theorem prime_liesOver_bot_map_eq_bot_localizationAtPrime_of_isDomain
    {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
    (N Q : Ideal A) [N.IsPrime] [N.LiesOver (⊥ : Ideal R)] [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)] (hNQ : N ≤ Q) :
    N.map (algebraMap A (Localization.AtPrime Q)) = ⊥ :=
  minimalPrime_map_eq_bot_localizationAtPrime_of_isDomain N Q
    (prime_liesOver_bot_mem_minimalPrimes (R := R) N) hNQ

end EtaleFundamentalGroups

end

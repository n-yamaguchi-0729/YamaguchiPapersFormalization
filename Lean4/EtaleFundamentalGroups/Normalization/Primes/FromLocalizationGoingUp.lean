/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Primes.FromLocalization
import EtaleFundamentalGroups.Normalization.Primes.GoingUp

/-!
# Following a localized normalization branch to a larger global prime

This file combines inverse localization with going-up.  A chosen local
normalization branch over a height-one prime is recovered as a prime of the
original normalization, then followed to any prescribed larger prime of the
base.  The recovered prime relocalizes to the chosen branch and has the same
ramification index.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

/-- A normalization prime chosen after localizing at `p` comes from a prime
of the original normalization and that same prime can be followed to every
larger base prime `P`. -/
theorem exists_normalizationPrimes_over_largerPrime_of_localized
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (p P : Ideal A) [p.IsPrime] [P.IsPrime] (hpP : p ≤ P) :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) p
    ∀ q : Ideal (integralClosure (Localization.AtPrime p) L),
      q.IsPrime →
      q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime p)) →
      ∃ Q N : Ideal (integralClosure A L),
        Q.IsPrime ∧ Q.LiesOver p ∧
        localizedNormalizationPrime (K := K) (L := L) p Q = q ∧
        Q.ramificationIdx A = q.ramificationIdx (Localization.AtPrime p) ∧
        Q ≤ N ∧ N.IsPrime ∧ N.LiesOver P := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
  let : IsScalarTower A (Localization.AtPrime p) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) p
  intro q hq hqOver
  let Q := normalizationPrimeFromLocalization (K := K) (L := L) p q
  have hQPrime : Q.IsPrime :=
    normalizationPrimeFromLocalization_isPrime (K := K) (L := L) p q hq
  have hQOver : Q.LiesOver p :=
    normalizationPrimeFromLocalization_liesOver
      (K := K) (L := L) p q hq hqOver
  have hlocal : localizedNormalizationPrime (K := K) (L := L) p Q = q :=
    localizedNormalizationPrime_normalizationPrimeFromLocalization
      (K := K) (L := L) p q hq
  have hram : Q.ramificationIdx A =
      q.ramificationIdx (Localization.AtPrime p) :=
    (normalizationPrimeFromLocalization_ramificationIdx
      (K := K) (L := L) p q hq hqOver).symm
  let : Q.IsPrime := hQPrime
  let : Q.LiesOver p := hQOver
  obtain ⟨N, hQN, hNPrime, hNOver⟩ :=
    exists_normalizationPrime_over_largerPrime
      (L := L) p P hpP Q
  exact ⟨Q, N, hQPrime, hQOver, hlocal, hram, hQN, hNPrime, hNOver⟩

end EtaleFundamentalGroups

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.HeightTwo.UnitGlobalization
import EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-!
# Globalizing a ramification-index unit from height two

A normalization prime over a height-one divisor remains a prime after
localizing at every larger height-two prime, and that localization preserves
its ramification index.  Combining this with height-two detection of
nonunits globalizes the local ramification-index unit statement to the
generic point of the divisor.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

/-- If the localized normalization branch has unit ramification index at
every height-two prime strictly above a prime parameter, then the original
ramification index is a unit modulo that parameter. -/
theorem ramificationIdx_isUnit_mod_prime_of_heightTwo_localizations
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite A (integralClosure A L)]
    (t : A) (ht : Prime t)
    [CharZero (A ⧸ Ideal.span {t})]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {t})]
    (hlocal : ∀ (P : Ideal A) [P.IsPrime]
        (_hstrict : Ideal.span {t} < P) (_hheight : P.height = 2),
      letI : Algebra (Localization.AtPrime P) L :=
        localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
      letI : IsScalarTower A (Localization.AtPrime P) L :=
        localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
      let q := localizedNormalizationPrime (K := K) (L := L) P Q
      IsUnit
        ((q.ramificationIdx (Localization.AtPrime P) : ℕ) :
          Localization.AtPrime P)) :
    IsUnit
      ((Q.ramificationIdx A : ℕ) : A ⧸ Ideal.span {t}) := by
  apply isUnit_natCast_mod_prime_of_heightTwo_localizations
    t ht (Q.ramificationIdx A) (Ideal.ramificationIdx_pos Q A)
  intro P hP hstrict hheight
  let : P.IsPrime := hP
  let : Algebra (Localization.AtPrime P) L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  have hQP : Q.under A ≤ P := by
    rw [← Q.over_def (Ideal.span {t})]
    exact hstrict.le
  let q := localizedNormalizationPrime (K := K) (L := L) P Q
  have hram : q.ramificationIdx (Localization.AtPrime P) =
      Q.ramificationIdx A :=
    localizedNormalizationPrime_ramificationIdx_of_under_le
      (K := K) (L := L) P Q hQP
  have hu := hlocal P hstrict hheight
  change IsUnit
    ((q.ramificationIdx (Localization.AtPrime P) : ℕ) :
      Localization.AtPrime P) at hu
  rw [hram] at hu
  simpa only [map_natCast] using hu

end EtaleFundamentalGroups

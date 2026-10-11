/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Localization.Basic
import Mathlib.RingTheory.Localization.AtPrime.Extension

/-!
# Primes in a localized normalization

This file transports a prime of a normalization lying over `P` to the
normalization after localizing the base at `P`.  The construction uses the
canonical normalization inclusion from `NormalizationLocalization` and the
general prime-localization API; it does not require the original
normalization to be a Dedekind domain.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

section Prime

variable (P : Ideal A) [P.IsPrime]

/-- The extension of a normalization prime to the normalization after
localizing the base at `P`. -/
noncomputable def localizedNormalizationPrime
    (Q : Ideal (integralClosure A L)) :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    Ideal (integralClosure (Localization.AtPrime P) L) :=
  by
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI : IsScalarTower A (Localization.AtPrime P) L :=
      localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    exact Q.map (integralClosureLocalizationRingHom (L := L) P)

omit [IsDomain A] in
/-- A prime above `P` remains prime in the localized normalization. -/
private theorem localizedNormalizationPrime_isPrime
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    (localizedNormalizationPrime (K := K) (L := L) P Q).IsPrime := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  change (Q.map (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).IsPrime
  exact IsLocalization.AtPrime.isPrime_map_of_liesOver
    (integralClosure A L) P
    (integralClosure (Localization.AtPrime P) L) Q

omit [IsDomain A] in
/-- The localized normalization prime lies over the maximal ideal of the
prime localization of the base. -/
theorem localizedNormalizationPrime_liesOver
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    (localizedNormalizationPrime (K := K) (L := L) P Q).LiesOver
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <|
        IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L x
  change (Q.map (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).LiesOver
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))
  exact IsLocalization.AtPrime.liesOver_map_of_liesOver
    P (Localization.AtPrime P)
    (integralClosure (Localization.AtPrime P) L) Q

omit [IsDomain A] in
/-- The localized normalization prime is maximal. -/
theorem localizedNormalizationPrime_isMaximal
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    (localizedNormalizationPrime (K := K) (L := L) P Q).IsMaximal := by
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  change Qlocal.IsMaximal
  let : Qlocal.IsPrime :=
    localizedNormalizationPrime_isPrime (K := K) (L := L) P Q
  let : Qlocal.LiesOver
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  exact Ideal.IsMaximal.of_liesOver_isMaximal Qlocal
    (IsLocalRing.maximalIdeal (Localization.AtPrime P))

omit [IsDomain A] in
/-- Localization at `P` preserves the ramification index of a normalization
prime above `P`. -/
theorem localizedNormalizationPrime_ramificationIdx
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    (localizedNormalizationPrime (K := K) (L := L) P Q).ramificationIdx
        (Localization.AtPrime P) =
      Q.ramificationIdx A := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <|
        IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L x
  change (Q.map (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).ramificationIdx
      (Localization.AtPrime P) = Q.ramificationIdx A
  exact IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx
    P (Localization.AtPrime P)
    (integralClosure (Localization.AtPrime P) L) Q

end Prime

end EtaleFundamentalGroups

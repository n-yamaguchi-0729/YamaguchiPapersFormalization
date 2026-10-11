/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.Primes.Basic

/-!
# Recovering a normalization prime from its localization

A prime of the normalization over `A_P` contracts to a prime of the original
normalization.  When the localized prime lies over the closed point of `A_P`,
that contraction lies over `P`; localizing it again recovers the original
prime and preserves its ramification index.

This is the inverse direction to `localizedNormalizationPrime`, needed when
all primes over the height-one DVR are first assembled locally and must then
be tied back to the original normalization.
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

/-- The contraction to the original normalization of a prime in the
normalization after localizing `A` at `P`. -/
noncomputable def normalizationPrimeFromLocalization
    :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    Ideal (integralClosure (Localization.AtPrime P) L) →
      Ideal (integralClosure A L) := by
  letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  letI := integralClosureLocalizationAlgebra (L := L) P
  exact fun q ↦ q.under (integralClosure A L)

omit [IsDomain A] in
/-- Contraction of a localized normalization prime is prime. -/
theorem normalizationPrimeFromLocalization_isPrime
    :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    ∀ q : Ideal (integralClosure (Localization.AtPrime P) L), q.IsPrime →
      (normalizationPrimeFromLocalization (K := K) (L := L) P q).IsPrime := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  intro q hq
  let : q.IsPrime := hq
  change (q.comap (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).IsPrime
  infer_instance

omit [IsDomain A] in
/-- If the localized prime lies over the closed point of `A_P`, its
contraction to the original normalization lies over `P`. -/
theorem normalizationPrimeFromLocalization_liesOver
    :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    ∀ q : Ideal (integralClosure (Localization.AtPrime P) L),
      q.IsPrime →
      q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime P)) →
      (normalizationPrimeFromLocalization (K := K) (L := L) P q).LiesOver P := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  intro q hq hqOver
  let : q.IsPrime := hq
  let : q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime P)) := hqOver
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <| IsScalarTower.algebraMap_apply A
        (Localization.AtPrime P) L x
  let : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).LiesOver P :=
    inferInstance
  let : q.LiesOver P := Ideal.LiesOver.trans q
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) P
  let : q.LiesOver
      (normalizationPrimeFromLocalization (K := K) (L := L) P q) := by
    change q.LiesOver
      (q.comap (algebraMap (integralClosure A L)
        (integralClosure (Localization.AtPrime P) L)))
    infer_instance
  exact Ideal.LiesOver.tower_bot q
    (normalizationPrimeFromLocalization (K := K) (L := L) P q) P

omit [IsDomain A] in
/-- Localizing the recovered contraction gives back the original localized
normalization prime. -/
theorem localizedNormalizationPrime_normalizationPrimeFromLocalization
    :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    ∀ q : Ideal (integralClosure (Localization.AtPrime P) L), q.IsPrime →
      localizedNormalizationPrime (K := K) (L := L) P
          (normalizationPrimeFromLocalization (K := K) (L := L) P q) = q := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  intro q hq
  let : q.IsPrime := hq
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  change (q.under (integralClosure A L)).map
    (algebraMap (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L)) = q
  exact IsLocalization.map_under
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    (integralClosure (Localization.AtPrime P) L) q

omit [IsDomain A] in
/-- Recovering a prime from the localized normalization and localizing again
identifies its local ramification index with the global one. -/
theorem normalizationPrimeFromLocalization_ramificationIdx
    :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    ∀ q : Ideal (integralClosure (Localization.AtPrime P) L),
      q.IsPrime →
      q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime P)) →
      q.ramificationIdx (Localization.AtPrime P) =
        (normalizationPrimeFromLocalization (K := K) (L := L) P q).ramificationIdx A := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  intro q hq hqOver
  let : q.IsPrime := hq
  let : q.LiesOver (IsLocalRing.maximalIdeal (Localization.AtPrime P)) := hqOver
  let Q := normalizationPrimeFromLocalization (K := K) (L := L) P q
  let : Q.IsPrime :=
    normalizationPrimeFromLocalization_isPrime (K := K) (L := L) P q hq
  let : Q.LiesOver P :=
    normalizationPrimeFromLocalization_liesOver (K := K) (L := L) P q hq hqOver
  have hlocal : localizedNormalizationPrime (K := K) (L := L) P Q = q :=
    localizedNormalizationPrime_normalizationPrimeFromLocalization
      (K := K) (L := L) P q hq
  calc
    q.ramificationIdx (Localization.AtPrime P) =
        (localizedNormalizationPrime (K := K) (L := L) P Q).ramificationIdx
          (Localization.AtPrime P) := congrArg
            (fun I : Ideal (integralClosure (Localization.AtPrime P) L) ↦
              I.ramificationIdx (Localization.AtPrime P)) hlocal.symm
    _ = Q.ramificationIdx A :=
      localizedNormalizationPrime_ramificationIdx
        (K := K) (L := L) P Q

end Prime

end EtaleFundamentalGroups

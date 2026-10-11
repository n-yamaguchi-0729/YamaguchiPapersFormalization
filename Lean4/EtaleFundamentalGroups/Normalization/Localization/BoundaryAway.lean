/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Away.TensorBaseChange
import EtaleFundamentalGroups.Normalization.Localization.Basic

/-!
# Boundary-away etaleness after localizing a normalization

Normalization in a fixed field extension commutes with localization of the
base.  The resulting square is a pushout, so an etale map on a principal
open of the original normalization remains etale after localization at an
arbitrary prime.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

/-- The primitive boundary-away map for a normalization survives
localization of the base at a prime. -/
theorem normalizationLocalization_boundaryAway
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal A) [P.IsPrime]
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A L)) f).Etale) :
    let R := Localization.AtPrime P
    letI : Algebra R L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI : IsScalarTower A R L :=
      localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    RingHom.Etale
      (R := Localization.Away (algebraMap A R f))
      (S := Localization.Away
        (algebraMap R (integralClosure R L) (algebraMap A R f)))
      (Localization.awayMap
        (algebraMap R (integralClosure R L)) (algebraMap A R f)) := by
  dsimp only
  let R := Localization.AtPrime P
  let : Algebra R L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A R L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure R L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let : Algebra A (integralClosure R L) :=
    ((algebraMap R (integralClosure R L)).comp
      (algebraMap A R)).toAlgebra
  let : IsScalarTower A R (integralClosure R L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (integralClosure A L)
      (integralClosure R L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    change algebraMap R L (algebraMap A R x) = algebraMap A L x
    exact (IsScalarTower.algebraMap_apply A R L x).symm
  let : Algebra.IsPushout A (integralClosure A L) R
      (integralClosure R L) :=
    Algebra.isPushout_of_isLocalization P.primeCompl R
      (integralClosure A L) (integralClosure R L)
  exact localization_awayMap_etale_of_isPushout
    (A := A) (B := integralClosure A L) (C := R)
      (D := integralClosure R L) f hAway

end EtaleFundamentalGroups

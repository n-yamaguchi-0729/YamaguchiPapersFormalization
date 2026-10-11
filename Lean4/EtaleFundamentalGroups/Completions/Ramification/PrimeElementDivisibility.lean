/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Coset.Card
import EtaleFundamentalGroups.Inertia.Localized.Cardinality
import EtaleFundamentalGroups.Kummer.Completions.RegularPair.RootPrimeDVR

/-!
# Ramification divisibility at a complete prime element

The usual normalization-inertia comparison in this project obtains a DVR
from regularity and a height-one calculation.  A maximal-adically separated
local domain needs neither global Noetherianity nor regularity at a principal
prime: separatedness rules out a nonzero prime strictly below that principal
prime, so its localization is a DVR.

This file feeds that source-produced DVR into the Dedekind-domain inertia
calculation.  It is the form needed over a finite-etale residue lift of a
maximal-adic completion, where no global `IsNoetherianRing` instance is
available.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe uA uK uL

/-- In a finite Galois extension, ramification at a prime element of a
maximal-adically separated local domain divides the field degree.

The DVR structure on the localization at `(y)` is generated internally from
`Prime y` and adic separatedness.  In particular, this theorem has no
regularity, height, or Noetherian hypothesis. -/
theorem normalization_ramificationIdx_dvd_finrank_of_prime_isHausdorff
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsHausdorff (maximalIdeal A) A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (y : A) (hy : Prime y) :
    let P := Ideal.span ({y} : Set A)
    letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
    ∀ (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
      [CharZero (A ⧸ P)],
      Q.ramificationIdx A ∣ Module.finrank K L := by
  dsimp only
  let P := Ideal.span ({y} : Set A)
  let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
  intro Q _ _ _
  let V := Localization.AtPrime P
  obtain ⟨hVDomain, hVDVR⟩ :=
    Kummer.exists_isDiscreteValuationRing_localizationAtPrime_of_prime_isHausdorff
      hy
  let : IsDomain V := hVDomain
  let : IsDiscreteValuationRing V := hVDVR
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
  let Bp := integralClosure V L
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let p := maximalIdeal V
  let : IsFractionRing Bp L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L Bp
  let : IsDedekindDomain Bp :=
    IsIntegralClosure.isDedekindDomain V K L Bp
  let : Module.Finite V Bp :=
    IsIntegralClosure.finite V K L Bp
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.IsTorsionFree V Bp :=
    IsIntegralClosure.isTorsionFree V L
  let : Finite Gal(L/K) :=
    IsGaloisGroup.finite Gal(L/K) K L
  let : IsGaloisGroup Gal(L/K) V Bp :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) V Bp K L
  let : Qlocal.LiesOver p :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : Algebra.IsSeparable (V ⧸ p) (Bp ⧸ Qlocal) :=
    localizedNormalizationResidue_isSeparable (K := K) (L := L) P Q
  have hp : p ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field V
  have hcard :
      Nat.card
          (localizedNormalizationInertia (K := K) (L := L) P Q) =
        Q.ramificationIdx A := by
    change
      Nat.card (Qlocal.toAddSubgroup.inertia Gal(L/K)) =
        Q.ramificationIdx A
    calc
      Nat.card (Qlocal.toAddSubgroup.inertia Gal(L/K)) =
          Qlocal.ramificationIdx V :=
        HilbertRamification.Dedekind.inertia_card_eq_ramificationIdx
          (A := V) (B := Bp) p Qlocal Gal(L/K) hp
      _ = Q.ramificationIdx A :=
        localizedNormalizationPrime_ramificationIdx
          (K := K) (L := L) P Q
  have hdiv :
      Nat.card (localizedNormalizationInertia (K := K) (L := L) P Q) ∣
        Nat.card Gal(L/K) :=
    Subgroup.card_dvd_of_injective
      (localizedNormalizationInertia (K := K) (L := L) P Q).subtype
      (localizedNormalizationInertia (K := K) (L := L) P Q).subtype_injective
  rw [hcard, IsGalois.card_aut_eq_finrank] at hdiv
  exact hdiv

end EtaleFundamentalGroups

end

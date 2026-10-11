/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import EtaleFundamentalGroups.Kummer.SelectedRoot.PrimeParameterLocalization
import EtaleFundamentalGroups.Normalization.Branch.GaloisRamification.AtLargerPrime

/-!
# Galois branch data after localization at a larger prime

For an active branch of a split strict-normal-crossings chart, this file
supplies the two local inputs used by the selected-root normalization theorem:
every normalization ramification index divides the exact Galois root exponent,
and the twice-localized branch residue ring has characteristic zero.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe uA uK uL

private theorem prime_algebraMap_localizationAtPrime_of_mem
    {A : Type uA} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] {t : A} (ht : Prime t) (htP : t ∈ P) :
    Prime (algebraMap A (Localization.AtPrime P) t) := by
  rcases prime_or_isUnit_algebraMap_localizationAtPrime P ht with
    hprime | hunit
  · exact hprime
  · have htCompl : t ∈ P.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime P) P t).mp hunit
    exact (htCompl htP).elim

/-- After first localizing at a larger prime containing an active branch,
every prime in the local normalization has ramification index dividing the
exact Galois exponent assigned to that branch.  The divisibility is sourced
from equality with the original common Galois branch index. -/
theorem
    localNormalizationPrime_ramificationIdx_dvd_splitStrictNormalCrossingsGaloisIndex_at_largerPrime
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r)
    (P : Ideal A) [P.IsPrime] (htjP : t j ∈ P) :
    let p₀ := Ideal.span ({t j} : Set A)
    letI : p₀.IsPrime :=
      Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 j hj)
    let R := Localization.AtPrime P
    letI : Algebra R K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI : Algebra R L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI : IsScalarTower R K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) P
    letI : IsFractionRing R K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) P
    let pR := p₀.map (algebraMap A R)
    letI : pR.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime P
      (P.span_singleton_le_iff_mem.mpr htjP)
    let V := Localization.AtPrime pR
    letI : Algebra V K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) pR
    letI : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR
    letI : IsScalarTower V K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) pR
    let C := integralClosure V L
    ∀ Q : (IsLocalRing.maximalIdeal V).primesOver C,
      Q.1.ramificationIdx V ∣
        splitStrictNormalCrossingsGaloisRamificationIndex
          (K := K) (L := L) t hNC j := by
  dsimp only
  let p₀ := Ideal.span ({t j} : Set A)
  let : p₀.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 j hj)
  let R := Localization.AtPrime P
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra R L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower R K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let pR := p₀.map (algebraMap A R)
  let : pR.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime P
    (P.span_singleton_le_iff_mem.mpr htjP)
  let V := Localization.AtPrime pR
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) pR
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) pR
  let C := integralClosure V L
  have hp₀ : p₀.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr
        (hNC.2.2.2.1 j hj).ne_zero)
      (hNC.2.2.2.1 j hj).not_isUnit
  have hp₀P : p₀ ≤ P := P.span_singleton_le_iff_mem.mpr htjP
  intro Q
  rw [localNormalizationPrime_ramificationIdx_eq_galoisBranchIndex_at_largerPrime
    (K := K) (L := L) p₀ P hp₀ hp₀P Q]
  rw [splitStrictNormalCrossingsGaloisRamificationIndex_eq
    (K := K) (L := L) t hNC j hj]
  exact dvd_rfl

/-- Characteristic zero of an active branch residue ring survives both
localization at a larger prime and localization at the image of the branch.
The target is the literal residue ring of the branch DVR used downstream. -/
theorem
    charZero_twiceLocalized_splitStrictNormalCrossingsBranchResidue
    {A : Type uA} [CommRing A] [IsDomain A] [IsLocalRing A]
    {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r)
    (P : Ideal A) [P.IsPrime] (htjP : t j ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t j} : Set A))) :
    let R := Localization.AtPrime P
    let p := algebraMap A R (t j)
    let hp : Prime p :=
      prime_algebraMap_localizationAtPrime_of_mem P
        (hNC.2.2.2.1 j hj) htjP
    let pR := Ideal.span ({p} : Set R)
    letI : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    let V := Localization.AtPrime pR
    CharZero (V ⧸ IsLocalRing.maximalIdeal V) := by
  dsimp only
  let R := Localization.AtPrime P
  let p : R := algebraMap A R (t j)
  have hp : Prime p :=
    prime_algebraMap_localizationAtPrime_of_mem P
      (hNC.2.2.2.1 j hj) htjP
  let pR := Ideal.span ({p} : Set R)
  let : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let V := Localization.AtPrime pR
  let : CharZero (R ⧸ Ideal.span ({p} : Set R)) :=
    charZero_quotient_algebraMap_localizationAtPrime P
      (hNC.2.2.2.1 j hj) htjP hCharZero
  let pV : V := algebraMap R V p
  let : CharZero (V ⧸ Ideal.span ({pV} : Set V)) :=
    charZero_quotient_algebraMap_localizationAtPrime pR hp
      (Ideal.mem_span_singleton_self p) inferInstance
  have hmax : IsLocalRing.maximalIdeal V =
      Ideal.span ({pV} : Set V) :=
    localizationAtPrime_maximalIdeal_eq_span_of_eq_span pR p rfl
  rw [hmax]
  infer_instance

end EtaleFundamentalGroups.Kummer

end

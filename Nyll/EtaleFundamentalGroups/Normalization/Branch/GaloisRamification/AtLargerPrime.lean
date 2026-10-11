/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Branch.GaloisRamificationIndex
import Nyll.EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime
import Nyll.EtaleFundamentalGroups.Normalization.Primes.FromLocalization

/-!
# Galois branch indices after localization at a larger prime

Localizing first at a prime containing a height-one branch, and then at the
image of that branch, does not change the common ramification index of a
finite Galois normalization.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

/-- Every normalization prime above a height-one branch has the original
common Galois ramification index, even when the branch DVR is obtained by
first localizing the base at a larger prime. -/
theorem localNormalizationPrime_ramificationIdx_eq_galoisBranchIndex_at_largerPrime
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p P : Ideal A) [p.IsPrime] [P.IsPrime]
    (hp : p.height = 1) (hpP : p ≤ P) :
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
    let pR := p.map (algebraMap A R)
    letI : pR.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime P hpP
    let V := Localization.AtPrime pR
    letI : Algebra V K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) pR
    letI : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR
    letI : IsScalarTower V K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) pR
    let C := integralClosure V L
    ∀ q : (IsLocalRing.maximalIdeal V).primesOver C,
      q.1.ramificationIdx V =
        normalizationGaloisBranchRamificationIndex
          (K := K) (L := L) p := by
  dsimp only
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
  let : IsScalarTower A R L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let pR := p.map (algebraMap A R)
  let : pR.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime P hpP
  let V := Localization.AtPrime pR
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) pR
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) pR
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) pR
  intro q
  let qV : Ideal (integralClosure V L) := q.1
  let : qV.IsPrime := by
    dsimp only [qV]
    infer_instance
  let : qV.LiesOver (IsLocalRing.maximalIdeal V) := by
    dsimp only [qV]
    infer_instance
  let qR : Ideal (integralClosure R L) :=
    normalizationPrimeFromLocalization (K := K) (L := L) pR qV
  have hqRPrime : qR.IsPrime :=
    normalizationPrimeFromLocalization_isPrime
      (K := K) (L := L) pR qV inferInstance
  let : qR.IsPrime := hqRPrime
  have hqROver : qR.LiesOver pR :=
    normalizationPrimeFromLocalization_liesOver
      (K := K) (L := L) pR qV inferInstance inferInstance
  let : qR.LiesOver pR := hqROver
  let qA : Ideal (integralClosure A L) :=
    normalizationPrimeFromLocalization (K := K) (L := L) P qR
  have hqAPrime : qA.IsPrime :=
    normalizationPrimeFromLocalization_isPrime
      (K := K) (L := L) P qR inferInstance
  let : qA.IsPrime := hqAPrime
  have hpRUnder : pR.under A = p :=
    Ideal.under_map_of_isLocalizationAtPrime P hpP
  have hqAEq : qA = qR.under (integralClosure A L) := by
    rfl
  let : IsScalarTower A (integralClosure A L) (integralClosure R L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A R (integralClosure R L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <| IsScalarTower.algebraMap_apply A R L x
  have hqAUnder : qA.under A = p := by
    rw [hqAEq]
    rw [Ideal.under_under, ← Ideal.under_under (B := R), ← hqROver.over,
      hpRUnder]
  have hqAP : qA.under A ≤ P := by
    rw [hqAUnder]
    exact hpP
  have hlocalA :
      localizedNormalizationPrime (K := K) (L := L) P qA = qR :=
    localizedNormalizationPrime_normalizationPrimeFromLocalization
      (K := K) (L := L) P qR inferInstance
  have hqAOver : qA.LiesOver p := ⟨hqAUnder.symm⟩
  let : qA.LiesOver p := hqAOver
  change Ideal.ramificationIdx (S := integralClosure V L) qV
      (Localization.AtPrime pR) =
    normalizationGaloisBranchRamificationIndex (K := K) (L := L) p
  calc
    Ideal.ramificationIdx (S := integralClosure V L) qV
        (Localization.AtPrime pR) =
        (normalizationPrimeFromLocalization
          (K := K) (L := L) pR qV).ramificationIdx R :=
      normalizationPrimeFromLocalization_ramificationIdx
        (K := K) (L := L) pR qV inferInstance inferInstance
    _ = qR.ramificationIdx R := by rfl
    _ = (localizedNormalizationPrime (K := K) (L := L) P qA).ramificationIdx R :=
      congrArg (fun I : Ideal (integralClosure R L) ↦ I.ramificationIdx R)
        hlocalA.symm
    _ = qA.ramificationIdx A :=
      localizedNormalizationPrime_ramificationIdx_of_under_le
        (K := K) (L := L) P qA hqAP
    _ = normalizationGaloisBranchRamificationIndex
        (K := K) (L := L) p :=
      normalizationPrime_ramificationIdx_eq_galoisBranchIndex
        (K := K) (L := L) p hp qA

end EtaleFundamentalGroups

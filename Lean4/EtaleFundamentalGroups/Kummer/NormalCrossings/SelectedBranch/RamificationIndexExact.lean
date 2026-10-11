/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Chosen.GenericComponentTarget
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.BranchAtLargerPrime

/-!
# Exact ramification index on a selected Galois branch

This leaf retains the equality which lies behind the divisibility interface
used by the selected-root theorem.  It also records the formal passage of an
exact ideal-theoretic ramification index to the complete valued target chosen
from the corresponding completed generic component.
-/

noncomputable section

open ValuationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace EtaleFundamentalGroups.Kummer

universe uA uK uL uV uC

/-- After localization at a larger prime and then at an active branch, every
prime of the normalization has ramification index equal to the common Galois
index prescribed for that branch. -/
theorem
    localNormalizationPrime_ramificationIdx_eq_splitStrictNormalCrossingsGaloisIndex_at_largerPrime
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
      Q.1.ramificationIdx V =
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
  rfl

/-- An exact ramification-index identification for a normalization prime is
transported unchanged to the complete valued target selected from its
completed generic component. -/
theorem exists_completedChosenGenericComponent_completeDVF_ramificationIndex_eq
    {V : Type uV} {C : Type uC} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra K L] [IsScalarTower V K L]
    (Q : (IsLocalRing.maximalIdeal V).primesOver C)
    (N : ℕ) (hQ : Q.1.ramificationIdx V = N) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : IsLocalHom (algebraMap V Vhat) :=
      standardDVRToCompletion_isLocalHom V K
    letI : Module.FaithfullyFlat V Vhat :=
      standardDVRCompletionValuationSubring_faithfullyFlat
        (V := V) (K := K)
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
    letI : Algebra V Khat :=
      standardDVFCompletionBaseAlgebra (V := V) (K := K)
    letI : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    letI : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    letI : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let m := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    letI : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let L₀ := GenericTensorFieldComponent m
    ∃ target : CompleteDVF.{_, 0} L₀,
      ∃ hExt : H.valuation.HasExtension target.valuation,
        letI : H.valuation.HasExtension target.valuation := hExt
        Module.Finite Vhat target.valuationSubring ∧
          ramificationIndex H.toDVF target.toDVF = N := by
  simpa only [hQ] using
    (exists_completedChosenGenericComponent_completeDVF
      (V := V) (C := C) (K := K) (L := L) Q)

end EtaleFundamentalGroups.Kummer

end

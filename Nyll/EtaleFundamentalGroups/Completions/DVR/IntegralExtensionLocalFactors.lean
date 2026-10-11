/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.EtaleFundamentalGroups.Completions.Adic.IntegralExtensionLocalFactors
import Nyll.EtaleFundamentalGroups.Completions.Adic.MappedIdeal
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.CompletionAdic

/-!
# Completed local factors of a finite DVR extension

For a finite Dedekind extension `C / V`, base change to the actual valued-field
completion of the fraction field of `V` is the product of the completed local
rings at the primes of `C` above the closed point.  Each local completion is
then identified with the valuation subring in the actual valued-field
completion of the fraction field of `C` for that prime.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uV uC uK uL

variable {V : Type uV} {C : Type uC}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [CommRing C] [IsDedekindDomain C]
variable [Algebra V C] [Algebra.IsIntegral V C]
variable [Module.IsTorsionFree V C] [Module.Finite V C]
variable {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
variable {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]

/-- The valuation subring in the actual completion of the fraction field of
`C`, for the valuation defined by a prime `Q` above the closed point of `V`. -/
noncomputable abbrev completedPrimeValuationSubring
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) : Type uL :=
  let W := Localization.AtPrime Q.1
  let hp : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  let hQ : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp Q.1
  letI : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ W
  letI : Algebra W L :=
    localizationAtPrimeToFractionFieldAlgebra (K := L) Q.1
  letI : IsFractionRing W L :=
    localizationAtPrimeToFractionField_isFractionRing (K := L) Q.1
  (standardDVFCompletionCompleteDVF W L).valuationSubring

/-- The completion of the local ring at `Q` is the valuation subring in its
actual valued-field completion. -/
noncomputable def completedPrimeAdicEquivValuationSubring
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
        (Localization.AtPrime Q.1) ≃+*
      completedPrimeValuationSubring (L := L) Q := by
  let W := Localization.AtPrime Q.1
  have hp : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  have hQ : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp Q.1
  letI : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ W
  letI : Algebra W L :=
    localizationAtPrimeToFractionFieldAlgebra (K := L) Q.1
  letI : IsFractionRing W L :=
    localizationAtPrimeToFractionField_isFractionRing (K := L) Q.1
  letI : Algebra W (standardDVFCompletionValuationSubring W L) :=
    standardDVFCompletionValuationSubringAlgebra W L
  exact
    (standardDVRAdicCompletionEquivCompletionValuationSubring W L).toRingEquiv

/-- The canonical map from the integral extension to the completed valuation
subring selected by `Q`. -/
noncomputable def completedPrimeMap
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    C →+* completedPrimeValuationSubring (L := L) Q := by
  let W := Localization.AtPrime Q.1
  have hp : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  have hQ : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp Q.1
  letI : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ W
  letI : Algebra W L :=
    localizationAtPrimeToFractionFieldAlgebra (K := L) Q.1
  letI : IsFractionRing W L :=
    localizationAtPrimeToFractionField_isFractionRing (K := L) Q.1
  exact (standardDVRToCompletionValuationSubringMap W L).comp
    (algebraMap C W)

omit [Algebra.IsIntegral V C] in
/-- The completed factor map remembers the original prime: the completed
maximal ideal contracts exactly to `Q`. -/
theorem completedPrimeMap_comap_maximalIdeal
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    (IsLocalRing.maximalIdeal
      (completedPrimeValuationSubring (L := L) Q)).comap
        (completedPrimeMap (L := L) Q) = Q.1 := by
  let W := Localization.AtPrime Q.1
  have hp : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  have hQ : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp Q.1
  let : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ W
  let : Algebra W L :=
    localizationAtPrimeToFractionFieldAlgebra (K := L) Q.1
  let : IsFractionRing W L :=
    localizationAtPrimeToFractionField_isFractionRing (K := L) Q.1
  let F := standardDVFCompletionValuationSubring W L
  let : Algebra W F :=
    standardDVFCompletionValuationSubringAlgebra W L
  let : IsLocalHom (algebraMap W F) :=
    standardDVRToCompletion_isLocalHom W L
  change (IsLocalRing.maximalIdeal F).comap
      ((algebraMap W F).comp (algebraMap C W)) = Q.1
  rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
  exact IsLocalization.AtPrime.under_maximalIdeal W Q.1

/-- Base change of a finite Dedekind extension to the actual completion of
the base DVR splits canonically into its completed local factors. -/
noncomputable def completedDVRIntegralExtensionLocalFactorsRingEquiv :
    let p := IsLocalRing.maximalIdeal V
    let baseHat := standardDVFCompletionCompleteDVF V K
    letI : Algebra V baseHat.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    (baseHat.valuationSubring ⊗[V] C) ≃+*
      ∀ Q : p.primesOver C,
        completedPrimeValuationSubring (L := L) Q := by
  let p := IsLocalRing.maximalIdeal V
  have hp : p ≠ ⊥ := by
    simpa [p, ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  let baseHat := standardDVFCompletionCompleteDVF V K
  letI : Algebra V baseHat.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  let eBase : AdicCompletion p V ≃ₐ[V] baseHat.valuationSubring :=
    standardDVRAdicCompletionEquivCompletionValuationSubring V K
  let eTensor : (baseHat.valuationSubring ⊗[V] C) ≃ₐ[V]
      (AdicCompletion p V ⊗[V] C) :=
    Algebra.TensorProduct.congr eBase.symm (AlgEquiv.refl : C ≃ₐ[V] C)
  let eMapped : (AdicCompletion p V ⊗[V] C) ≃+*
      AdicCompletion (p.map (algebraMap V C)) C :=
    tensorProductMappedIdealCompletionFreeRingEquiv
      (R₀ := V) (S₀ := C) p
  let eLocal :=
    adicCompletionIntegralExtensionLocalFactorsRingEquiv
      (A := V) (B := C) p hp
  let eActual :
      (∀ Q : p.primesOver C,
        AdicCompletion
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
          (Localization.AtPrime Q.1)) ≃+*
      (∀ Q : p.primesOver C,
        completedPrimeValuationSubring (L := L) Q) :=
    RingEquiv.piCongrRight fun Q =>
      completedPrimeAdicEquivValuationSubring (L := L) Q
  exact eTensor.toRingEquiv.trans (eMapped.trans (eLocal.trans eActual))

/-- On the right tensor factor, the global product decomposition is exactly
the canonical map into the completed local factor selected by `Q`. -/
@[simp]
theorem completedDVRIntegralExtensionLocalFactorsRingEquiv_includeRight_apply
    (x : C) (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let baseHat := standardDVFCompletionCompleteDVF V K
    letI : Algebra V baseHat.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    completedDVRIntegralExtensionLocalFactorsRingEquiv
        (V := V) (C := C) (K := K) (L := L)
        (Algebra.TensorProduct.includeRight x) Q =
      completedPrimeMap (L := L) Q x := by
  let p := IsLocalRing.maximalIdeal V
  have hp : p ≠ ⊥ := by
    simpa [p, ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  have hQ : Q.1 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp Q.1
  let W := Localization.AtPrime Q.1
  let : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hQ W
  let : Algebra W L :=
    localizationAtPrimeToFractionFieldAlgebra (K := L) Q.1
  let : IsFractionRing W L :=
    localizationAtPrimeToFractionField_isFractionRing (K := L) Q.1
  dsimp only [completedDVRIntegralExtensionLocalFactorsRingEquiv,
    completedPrimeMap, completedPrimeAdicEquivValuationSubring]
  simp only [RingEquiv.trans_apply, RingEquiv.piCongrRight_apply,
    AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
    map_one,
    adicCompletionIntegralExtensionLocalFactorsRingEquiv_apply]
  rw [← Algebra.TensorProduct.includeRight_apply,
    tensorProductMappedIdealCompletionFreeRingEquiv_includeRight_apply,
    adicCompletionIntegralExtensionEquivPi_of,
    adicCompletionPrimePowerLocalFactorAlgEquiv_of]
  change standardDVRAdicCompletionEquivCompletionValuationSubring
      (Localization.AtPrime Q.1) L
        (AdicCompletion.of
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q.1))
          (Localization.AtPrime Q.1)
          (algebraMap C (Localization.AtPrime Q.1) x)) =
    standardDVRToCompletionValuationSubringMap
      (Localization.AtPrime Q.1) L
        (algebraMap C (Localization.AtPrime Q.1) x)
  rw [standardDVRAdicCompletionEquivCompletionValuationSubring_apply_of]
  rfl

end EtaleFundamentalGroups

end

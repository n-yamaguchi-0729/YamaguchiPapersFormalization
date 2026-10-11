/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.ValuationRing
import EtaleFundamentalGroups.Completions.Retained.Component.LocalizationFractionRing
import EtaleFundamentalGroups.LocalGeometry.DVR.FiniteToStandardDVF
import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-!
# Ramification in the normalization of a retained completed component

Let `N ≤ Q` be the generic/branch part of a retained completed tensor-prime
chain.  The localization at `Q` is assumed to have already been
source-produced as a DVR.  Its fraction field is the literal tensor
component selected by `N`, by
`retainedCompletedChosenComponentLocalization_isFractionRing`.

If `qhat` is a prime of the normalization of that same component lying over
`Q`, its local ring has the same fraction field.  The canonical local map
from the DVR at `Q` to the normalization local ring is an isomorphism: in a
valuation ring every fraction, or its inverse, is integral, and locality of
the map rules out the inverse-only case.  Thus the normalization step has
vertical ramification index one, and the ramification index over the
completed base is unchanged.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uS uK uL uK'

private theorem maximalIdeal_ramificationIdx_eq_of_algEquiv
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsLocalRing B] [IsLocalRing C]
    (e : B ≃ₐ[A] C) :
    (IsLocalRing.maximalIdeal B).ramificationIdx A =
      (IsLocalRing.maximalIdeal C).ramificationIdx A := by
  let : Algebra B C := e.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  let eB : B ≃ₐ[B] C :=
    AlgEquiv.ofRingEquiv (R := B) (f := e.toRingEquiv) fun _ ↦ rfl
  let : IsLocalization (IsUnit.submonoid B) C :=
    IsLocalization.isLocalization_of_algEquiv (IsUnit.submonoid B) eB
  have hdisj : Disjoint
      ((IsUnit.submonoid B : Submonoid B) : Set B)
      (IsLocalRing.maximalIdeal B : Set B) := by
    rw [Set.disjoint_left]
    intro x hxunit hxmax
    exact ((IsLocalRing.mem_maximalIdeal x).mp hxmax) hxunit
  have hram := ramificationIdx_map_eq_of_isLocalization
    (R := A) (S := B) (R' := A) (S' := C)
    (IsUnit.submonoid A) (IsUnit.submonoid B)
    (IsLocalRing.maximalIdeal B) hdisj
  have hmap : (IsLocalRing.maximalIdeal B).map (algebraMap B C) =
      IsLocalRing.maximalIdeal C := by
    change (IsLocalRing.maximalIdeal B).map e.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal C
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  rw [hmap] at hram
  exact hram.symm

variable {R : Type uR} {R' : Type uR'} {S : Type uS}
variable [CommRing R] [IsDomain R]
variable [CommRing R'] [IsDomain R'] [Algebra R R']
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
variable {K' : Type uK'} [Field K'] [Algebra R' K']
variable [IsFractionRing R' K']
variable {K : Type uK} {L : Type uL}
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [IsScalarTower R S L]
variable [Algebra K L] [IsScalarTower R K L]
variable [Algebra R K'] [IsScalarTower R R' K']
variable [Algebra K K'] [IsScalarTower R K K']

/-- The local ring of the normalization of the retained component is the
same DVR as the retained tensor localization, and hence has exactly the
same ramification index over the completed base.

The local algebra equivalence is returned together with the numerical
equality.  Its fraction-field comparison, injectivity, and surjectivity are
all constructed internally; no kernel, fraction equivalence, or vertical
ramification equality is an input. -/
theorem
    retainedCompletedNormalizationAtPrime_localAlgEquiv_and_ramificationIdx_eq
    (N Q : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [Q.IsPrime] (hNQ : N ≤ Q)
    [IsDomain (Localization.AtPrime Q)]
    [IsDiscreteValuationRing (Localization.AtPrime Q)] :
    let T := R' ⊗[R] S
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Omega := GenericTensorFieldComponent m
    let r'OmegaAlgebra : Algebra R' Omega :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    letI : Algebra R' Omega := r'OmegaAlgebra
    letI : SMul R' Omega := r'OmegaAlgebra.toSMul
    letI : IsScalarTower R' K' Omega :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let IC := integralClosure R' Omega
    let jIC := retainedCompletedChosenNormalizationAlgHom
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : Algebra T IC := jIC.toAlgebra
    letI : IsScalarTower R' T IC :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (jIC.commutes x).symm
    ∀ (qhat : Ideal IC) [qhat.IsPrime] [qhat.LiesOver Q],
      let P := Q.under R'
      letI : P.IsPrime := inferInstance
      letI : Q.LiesOver P := Ideal.over_under (A := R') Q
      letI : qhat.LiesOver P := Ideal.LiesOver.trans qhat Q P
      let V := Localization.AtPrime P
      let W := Localization.AtPrime Q
      let D := Localization.AtPrime qhat
      letI : Algebra V W :=
        Localization.AtPrime.algebraOfLiesOver P Q
      letI : Algebra V D :=
        Localization.AtPrime.algebraOfLiesOver P qhat
      ∃ _ : W ≃ₐ[V] D,
        qhat.ramificationIdx R' = Q.ramificationIdx R' := by
  classical
  dsimp only
  intro qhat _ _
  let T := R' ⊗[R] S
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let Omega := GenericTensorFieldComponent m
  let r'OmegaAlgebra : Algebra R' Omega :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' Omega := r'OmegaAlgebra
  let : SMul R' Omega := r'OmegaAlgebra.toSMul
  let : IsScalarTower R' K' Omega :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let IC := integralClosure R' Omega
  let j := retainedCompletedChosenComponentAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let jIC := retainedCompletedChosenNormalizationAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : Algebra T Omega := j.toAlgebra
  let : Algebra T IC := jIC.toAlgebra
  let : IsScalarTower R' T IC :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (jIC.commutes x).symm
  let P := Q.under R'
  let : P.IsPrime := inferInstance
  let : Q.LiesOver P := Ideal.over_under (A := R') Q
  let : qhat.LiesOver P := Ideal.LiesOver.trans qhat Q P
  let V := Localization.AtPrime P
  let W := Localization.AtPrime Q
  let D := Localization.AtPrime qhat
  let : Algebra V W :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let : Algebra V D :=
    Localization.AtPrime.algebraOfLiesOver P qhat
  let : Algebra W D :=
    Localization.AtPrime.algebraOfLiesOver Q qhat
  let : IsLocalHom (algebraMap W D) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom
      Q qhat (algebraMap T IC) Ideal.LiesOver.over
  let : Algebra W Omega :=
    retainedCompletedChosenComponentLocalizationAlgebra
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
  let : IsScalarTower T W Omega :=
    retainedCompletedChosenComponentLocalization_isScalarTower
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
  let : IsFractionRing W Omega :=
    retainedCompletedChosenComponentLocalization_isFractionRing
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N Q hNQ
  let : FiniteDimensional K L :=
    fractionFields_finiteDimensional_of_moduleFinite
      (V := R) (W := S) (K := K) (L := L)
  let : IsScalarTower R' K' Omega := inferInstance
  let : IsFractionRing IC Omega :=
    IsIntegralClosure.isFractionRing_of_finite_extension R' K' Omega IC
  let : Algebra D Omega :=
    localizationAtPrimeToFractionFieldAlgebra (K := Omega) qhat
  let : IsScalarTower IC D Omega :=
    localizationAtPrimeToFractionField_isScalarTower
      (K := Omega) qhat
  let : IsFractionRing D Omega :=
    localizationAtPrimeToFractionField_isFractionRing
      (K := Omega) qhat
  let : IsScalarTower T IC Omega :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower T D Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply T IC Omega,
      IsScalarTower.algebraMap_apply T IC D,
      IsScalarTower.algebraMap_apply IC D Omega]
  let : IsScalarTower T W D := inferInstance
  have hTowerHom :
      (algebraMap D Omega).comp (algebraMap W D) =
        algebraMap W Omega := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    ext x
    · simp only [RingHom.comp_apply]
      change algebraMap D Omega
          (algebraMap W D
            (algebraMap T W
              ((Algebra.TensorProduct.includeLeft : R' →ₐ[R] T) x))) =
        algebraMap W Omega
          (algebraMap T W
            ((Algebra.TensorProduct.includeLeft : R' →ₐ[R] T) x))
      rw [← IsScalarTower.algebraMap_apply T W D,
        ← IsScalarTower.algebraMap_apply T D Omega,
        ← IsScalarTower.algebraMap_apply T W Omega]
    · simp only [RingHom.comp_apply]
      change algebraMap D Omega
          (algebraMap W D
            (algebraMap T W
              ((Algebra.TensorProduct.includeRight : S →ₐ[R] T) x))) =
        algebraMap W Omega
          (algebraMap T W
            ((Algebra.TensorProduct.includeRight : S →ₐ[R] T) x))
      rw [← IsScalarTower.algebraMap_apply T W D,
        ← IsScalarTower.algebraMap_apply T D Omega,
        ← IsScalarTower.algebraMap_apply T W Omega]
  let : IsScalarTower W D Omega :=
    IsScalarTower.of_algebraMap_eq' hTowerHom.symm
  have hWDInjective : Function.Injective (algebraMap W D) := by
    intro x y hxy
    apply IsFractionRing.injective W Omega
    rw [← hTowerHom]
    exact congrArg (algebraMap D Omega) hxy
  have hWDSurjective : Function.Surjective (algebraMap W D) := by
    intro d
    by_cases hd : d = 0
    · refine ⟨0, ?_⟩
      rw [map_zero, hd]
    let x : Omega := algebraMap D Omega d
    have hx : x ≠ 0 := by
      exact (map_ne_zero_iff _ (IsFractionRing.injective D Omega)).2 hd
    obtain ⟨w, hw⟩ | ⟨w, hw⟩ :=
      ValuationRing.isInteger_or_isInteger (R := W) x
    · refine ⟨w, ?_⟩
      apply IsFractionRing.injective D Omega
      simpa only [IsScalarTower.algebraMap_apply W D Omega] using hw
    · have hprodOmega :
          algebraMap D Omega (algebraMap W D w * d) =
            algebraMap D Omega 1 := by
        rw [map_mul, map_one,
          ← IsScalarTower.algebraMap_apply W D Omega, hw]
        exact inv_mul_cancel₀ hx
      have hprodD : algebraMap W D w * d = 1 :=
        (IsFractionRing.injective D Omega) hprodOmega
      have hunitMap : IsUnit (algebraMap W D w) := by
        rw [isUnit_iff_exists_inv]
        exact ⟨d, hprodD⟩
      have hunitW : IsUnit w :=
        (isUnit_map_iff (algebraMap W D) w).mp hunitMap
      rcases hunitW with ⟨u, rfl⟩
      refine ⟨↑u⁻¹, ?_⟩
      calc
        algebraMap W D (↑u⁻¹) =
            algebraMap W D (↑u⁻¹) * 1 := by simp
        _ = algebraMap W D (↑u⁻¹) *
              (algebraMap W D (↑u) * d) := by rw [hprodD]
        _ = d := by
          rw [← mul_assoc, ← map_mul]
          simp
  let eW : W ≃ₐ[W] D :=
    AlgEquiv.ofBijective (Algebra.ofId W D)
      ⟨hWDInjective, hWDSurjective⟩
  let eV : W ≃ₐ[V] D := eW.restrictScalars V
  have hQDisjoint :
      Disjoint (Q.primeCompl : Set T) (Q : Set T) :=
    Set.disjoint_compl_left_iff_subset.mpr le_rfl
  have hQlocal := ramificationIdx_map_eq_of_isLocalization
    (R := R') (S := T) (R' := V) (S' := W)
    P.primeCompl Q.primeCompl Q hQDisjoint
  have hQmap : Q.map (algebraMap T W) =
      IsLocalRing.maximalIdeal W :=
    Localization.AtPrime.map_eq_maximalIdeal
  rw [hQmap] at hQlocal
  have hqhatDisjoint :
      Disjoint (qhat.primeCompl : Set IC) (qhat : Set IC) :=
    Set.disjoint_compl_left_iff_subset.mpr le_rfl
  have hqhatLocal := ramificationIdx_map_eq_of_isLocalization
    (R := R') (S := IC) (R' := V) (S' := D)
    P.primeCompl qhat.primeCompl qhat hqhatDisjoint
  have hqhatMap : qhat.map (algebraMap IC D) =
      IsLocalRing.maximalIdeal D :=
    Localization.AtPrime.map_eq_maximalIdeal
  rw [hqhatMap] at hqhatLocal
  refine ⟨eV, ?_⟩
  calc
    qhat.ramificationIdx R' =
        (IsLocalRing.maximalIdeal D).ramificationIdx V :=
      hqhatLocal.symm
    _ = (IsLocalRing.maximalIdeal W).ramificationIdx V :=
      (maximalIdeal_ramificationIdx_eq_of_algEquiv eV).symm
    _ = Q.ramificationIdx R' := hQlocal

end EtaleFundamentalGroups

end

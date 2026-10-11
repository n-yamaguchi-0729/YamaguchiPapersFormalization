/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.GenericFiber.LiesOverFractionRingExtension
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.PrimeRootCover
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtaleTower
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.BranchAtLargerPrime
import Nyll.SchemeTheory.Divisors.NormalCrossings.HeightTwo.Parameters

/-!
# A fixed component at an active Galois root prime

This file applies the selected-root normalization descent theorem to any
active strict-normal-crossings branch through a height-two point.  A finite
faithful normal extension of the simple root cover and a prime above its root
prime determine the further local base.  All ramification divisibilities,
residue characteristic-zero facts, and fraction-field towers are produced
from the original Galois normalization and the finite extension.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL uD

private theorem prime_algebraMap_localizationAtPrime_of_mem_active
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

/-- A chosen fraction field `K` of `V` acts canonically on any field `F`
containing `V`, by transporting the literal fraction-ring lift across the
canonical fraction-field equivalence. -/
@[reducible]
private noncomputable def chosenFractionFieldToExtensionAlgebra
    {V : Type uA} {K : Type uK} {F : Type uD}
    [CommRing V] [IsDomain V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field F] [Algebra V F] [FaithfulSMul V F] : Algebra K F := by
  letI : Algebra (FractionRing V) F := FractionRing.liftAlgebra V F
  exact ((algebraMap (FractionRing V) F).comp
    (FractionRing.algEquiv V K).symm.toRingHom).toAlgebra

private theorem chosenFractionFieldToExtension_isScalarTower
    {V : Type uA} {K : Type uK} {F : Type uD}
    [CommRing V] [IsDomain V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field F] [Algebra V F] [FaithfulSMul V F] :
    letI : Algebra K F :=
      chosenFractionFieldToExtensionAlgebra (V := V) (K := K) (F := F)
    IsScalarTower V K F := by
  let : Algebra K F :=
    chosenFractionFieldToExtensionAlgebra (V := V) (K := K) (F := F)
  let : Algebra (FractionRing V) F := FractionRing.liftAlgebra V F
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap V F x =
    algebraMap (FractionRing V) F
      ((FractionRing.algEquiv V K).symm (algebraMap V K x))
  rw [← (FractionRing.algEquiv V K).commutes x,
    (FractionRing.algEquiv V K).symm_apply_apply]
  exact IsScalarTower.algebraMap_apply V (FractionRing V) F x

/-- The ramification-divisibility proposition, bundled over a prime-spectrum
point so equality of prime ideals transports all dependent localization data
at once. -/
private def localNormalizationRamificationDividesAtPrimeSpectrum
    {R : Type uA} {K : Type uK} {L : Type uL}
    [CommRing R] [IsDomain R]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (I : PrimeSpectrum R) (N : ℕ) : Prop :=
  let V := Localization.AtPrime I.asIdeal
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) I.asIdeal
  letI : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) I.asIdeal
  letI : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) I.asIdeal
  let C := integralClosure V L
  ∀ Q : (IsLocalRing.maximalIdeal V).primesOver C,
    Q.1.ramificationIdx V ∣ N

/-- The simple root cover attached to an active Galois branch at a
height-two point is a two-dimensional regular local domain, with prime root
and regular local quotient. -/
theorem splitStrictNormalCrossings_heightTwo_galoisSingleRootCover_geometry
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htjP : t j ∈ P) :
    let R := Localization.AtPrime P
    let p := algebraMap A R (t j)
    let N := splitStrictNormalCrossingsGaloisRamificationIndex
      (K := K) (L := L) t hNC j
    let g : R[X] := X ^ N - C p
    let S := AdjoinRoot g
    IsRegularLocalRing S ∧ IsDomain S ∧
      ringKrullDim S = ((2 : ℕ∞) : WithBot ℕ∞) ∧
      Prime (AdjoinRoot.root g) ∧
      IsDomain (S ⧸ Ideal.span ({AdjoinRoot.root g} : Set S)) ∧
      IsRegularLocalRing
        (S ⧸ Ideal.span ({AdjoinRoot.root g} : Set S)) := by
  dsimp only
  let R := Localization.AtPrime P
  let p : R := algebraMap A R (t j)
  have hp : Prime p :=
    prime_algebraMap_localizationAtPrime_of_mem_active P
      (hNC.2.2.2.1 j hj) htjP
  have hdimR : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim R = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P R
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  obtain ⟨z, hreg, hgen⟩ :=
    exists_regular_pair_localizationAtPrime_of_splitStrictNormalCrossings
      hNC j hj P hP htjP
  have hquot : IsRegularLocalRing
      (R ⧸ Ideal.span ({p} : Set R)) :=
    (quotient_geometry_of_mem_regularSystem hreg hgen (p := p)
      (by simp [p, R])).2
  exact heightTwoPrimeRootCover_geometry
    (splitStrictNormalCrossingsGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC j) hp hquot hdimR

/-- A finite faithful normal extension of an active simple Galois root cover
has etale normalization in every fixed generic tensor component at a prime
above the root prime.  The component `m` remains the literal component over
the original fraction field `K`; no intermediate component is exposed.
-/
theorem
    integralClosure_strictNormalCrossingsGaloisActiveRoot_fixedComponent_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (j : Fin d) (hj : j.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htjP : t j ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t j} : Set A))) :
    let R := Localization.AtPrime P
    let p := algebraMap A R (t j)
    let N := splitStrictNormalCrossingsGaloisRamificationIndex
      (K := K) (L := L) t hNC j
    let g : R[X] := X ^ N - C p
    let S := AdjoinRoot g
    let qS := Ideal.span ({AdjoinRoot.root g} : Set S)
    let hgeometryS :=
      splitStrictNormalCrossings_heightTwo_galoisSingleRootCover_geometry
        (K := K) (L := L) hNC j hj P hP htjP
    letI : IsRegularLocalRing S := hgeometryS.1
    letI : IsDomain S := hgeometryS.2.1
    letI : IsIntegrallyClosed S :=
      SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
        hgeometryS.2.2.1
    letI : qS.IsPrime :=
      Ideal.isPrime_span_singleton_of_prime hgeometryS.2.2.2.1
    let pR := Ideal.span ({p} : Set R)
    let hp : Prime p :=
      prime_algebraMap_localizationAtPrime_of_mem_active P
        (hNC.2.2.2.1 j hj) htjP
    letI : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    letI : qS.LiesOver pR :=
      span_root_liesOver_span_radicand
        (splitStrictNormalCrossingsGaloisRamificationIndex_pos
          (K := K) (L := L) t hNC j) hp
    let V := Localization.AtPrime pR
    let W := Localization.AtPrime qS
    letI : Algebra V W := Localization.AtPrime.algebraOfLiesOver pR qS
    letI : Module.Free R S :=
      (Polynomial.monic_X_pow_sub_C p
        (splitStrictNormalCrossingsGaloisRamificationIndex_pos
          (K := K) (L := L) t hNC j).ne').free_adjoinRoot
    letI : FaithfulSMul R S := inferInstance
    letI : Algebra R K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI : IsFractionRing R K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) P
    letI : Algebra V K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) pR
    letI : IsFractionRing V K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) pR
    ∀ {D : Type uD} [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
      [Algebra R D] [Algebra S D] [IsScalarTower R S D]
      [FaithfulSMul S D] [Module.Finite S D]
      (qD : Ideal D) [qD.IsPrime] [qD.LiesOver qS],
      let F := FractionRing D
      letI : FaithfulSMul R D := FaithfulSMul.trans R S D
      letI : FaithfulSMul R F := FaithfulSMul.trans R D F
      letI : Algebra K F :=
        chosenFractionFieldToExtensionAlgebra (V := R) (K := K) (F := F)
      letI : IsScalarTower R K F :=
        chosenFractionFieldToExtension_isScalarTower
          (V := R) (K := K) (F := F)
      ∀ (m : Ideal (F ⊗[K] L)) (hm : m.IsMaximal),
        letI : m.IsMaximal := hm
        let B := Localization.AtPrime qD
        let M := GenericTensorFieldComponent m
        letI : Algebra B M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := B) m
        Algebra.Etale B (integralClosure B M) := by
  dsimp only
  classical
  let R := Localization.AtPrime P
  let : IsRegularLocalRing R := inferInstance
  have hdimR : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim R = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P R
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  let : IsRegularRing R :=
    EtaleFundamentalGroups.isRegularRing_of_isRegularLocalRing_dimension_two hdimR
  let p : R := algebraMap A R (t j)
  have hp : Prime p :=
    prime_algebraMap_localizationAtPrime_of_mem_active P
      (hNC.2.2.2.1 j hj) htjP
  let : Fact (Prime p) := ⟨hp⟩
  let N := splitStrictNormalCrossingsGaloisRamificationIndex
    (K := K) (L := L) t hNC j
  have hN : 0 < N :=
    splitStrictNormalCrossingsGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC j
  let g : R[X] := X ^ N - C p
  let S := AdjoinRoot g
  let qS := Ideal.span ({AdjoinRoot.root g} : Set S)
  have hgeometryS :=
    splitStrictNormalCrossings_heightTwo_galoisSingleRootCover_geometry
      (K := K) (L := L) hNC j hj P hP htjP
  let : IsRegularLocalRing S := hgeometryS.1
  let : IsDomain S := hgeometryS.2.1
  let : IsIntegrallyClosed S :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hgeometryS.2.2.1
  let : qS.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hgeometryS.2.2.2.1
  let pR := Ideal.span ({p} : Set R)
  let : pR.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
  let : qS.LiesOver pR :=
    span_root_liesOver_span_radicand hN hp
  let V := Localization.AtPrime pR
  let W := Localization.AtPrime qS
  let : IsDiscreteValuationRing V :=
    EtaleFundamentalGroups.isDiscreteValuationRing_localizationAtSpan_of_prime
      R p hp
  let : Algebra V W := Localization.AtPrime.algebraOfLiesOver pR qS
  let : IsDomain W :=
    adjoinRootLocalizationAtRootPrime_isDomain hN hp
  let pV : V := algebraMap R V p
  let Rn := AdjoinRoot (X ^ N - C pV)
  let eLocal : Rn ≃ₐ[V] W :=
    adjoinRootLocalizationAtRootPrimeAlgEquiv hN hp
  let : Module.Free V Rn :=
    (Polynomial.monic_X_pow_sub_C pV hN.ne').free_adjoinRoot
  let : Module.Free V W := Module.Free.of_equiv eLocal.toLinearEquiv
  let K₀ := FractionRing V
  let Kroot := FractionRing W
  let : FaithfulSMul V W := inferInstance
  let : FaithfulSMul V Kroot := FaithfulSMul.trans V W Kroot
  let : Algebra K₀ Kroot := FractionRing.liftAlgebra V Kroot
  let : IsScalarTower V K₀ Kroot :=
    FractionRing.isScalarTower_liftAlgebra V Kroot
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra R L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower R K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) pR
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) pR
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) pR
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) pR
  let Cnorm := integralClosure V L
  let : IsFractionRing Cnorm L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L Cnorm
  let : IsDedekindDomain Cnorm :=
    IsIntegralClosure.isDedekindDomain V K L Cnorm
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.IsTorsionFree V Cnorm := by
    exact IsIntegralClosure.isTorsionFree V (A := Cnorm) L
  let : Module.Finite V Cnorm :=
    IsIntegralClosure.finite V K L Cnorm
  let : Algebra K₀ K := FractionRing.liftAlgebra V K
  let : IsScalarTower V K₀ K :=
    FractionRing.isScalarTower_liftAlgebra V K
  let : Algebra K₀ L :=
    fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
  let : IsScalarTower K₀ K L :=
    fractionRingToChosenFractionFieldToExtension_isScalarTower
      (V := V) (K := K) (L := L)
  let : IsScalarTower V K₀ L :=
    fractionRingToExtension_isScalarTower (V := V) (K := K) (L := L)
  let : FiniteDimensional K₀ L :=
    fractionRingToExtension_finiteDimensional
      (V := V) (K := K) (L := L)
  let : Algebra.IsSeparable K₀ L :=
    fractionRingToExtension_isSeparable (V := V) (K := K) (L := L)
  have hbranch :=
    localNormalizationPrime_ramificationIdx_dvd_splitStrictNormalCrossingsGaloisIndex_at_largerPrime
      (K := K) (L := L) hNC j hj P htjP
  have hdiv : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver Cnorm,
      Q.1.ramificationIdx V ∣ N := by
    let p₀ := Ideal.span ({t j} : Set A)
    let : p₀.IsPrime :=
      Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 j hj)
    have hp₀P : p₀ ≤ P := P.span_singleton_le_iff_mem.mpr htjP
    let IMap : PrimeSpectrum R :=
      ⟨p₀.map (algebraMap A R),
        Ideal.isPrime_map_of_isLocalizationAtPrime P hp₀P⟩
    let ISpan : PrimeSpectrum R := ⟨pR, inferInstance⟩
    have hI : IMap = ISpan := by
      apply PrimeSpectrum.ext
      dsimp only [IMap, ISpan, p₀, pR, p]
      rw [Ideal.map_span, Set.image_singleton]
    have hsource :
        localNormalizationRamificationDividesAtPrimeSpectrum
          (K := K) (L := L) IMap N := by
      simpa only [localNormalizationRamificationDividesAtPrimeSpectrum,
        IMap, p₀, R] using
        hbranch
    rw [hI] at hsource
    simpa only [localNormalizationRamificationDividesAtPrimeSpectrum,
      ISpan, V, Cnorm] using hsource
  have hCharZeroV : CharZero (V ⧸ IsLocalRing.maximalIdeal V) := by
    simpa only [R, p, pR, V] using
      (charZero_twiceLocalized_splitStrictNormalCrossingsBranchResidue
        hNC j hj P htjP hCharZero)
  intro D _ _ _ _ _ _ _ _ qD _ _
  let F := FractionRing D
  let : Module.Free R S :=
    (Polynomial.monic_X_pow_sub_C p hN.ne').free_adjoinRoot
  let : FaithfulSMul R S := inferInstance
  let : FaithfulSMul R D := FaithfulSMul.trans R S D
  let : FaithfulSMul R F := FaithfulSMul.trans R D F
  let : Algebra K F :=
    chosenFractionFieldToExtensionAlgebra (V := R) (K := K) (F := F)
  let : IsScalarTower R K F :=
    chosenFractionFieldToExtension_isScalarTower
      (V := R) (K := K) (F := F)
  let : Algebra V F :=
    localizationAtPrimeToExtensionAlgebra
      (A := R) (K := K) (L := F) pR
  let : IsScalarTower V K F :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (A := R) (K := K) (L := F) pR
  let : IsScalarTower R V F :=
    localizationAtPrimeToExtension_isScalarTower
      (A := R) (K := K) (L := F) pR
  let : IsScalarTower R S F := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R F x =
      algebraMap D F (algebraMap S D (algebraMap R S x))
    rw [← IsScalarTower.algebraMap_apply R S D]
    rfl
  let : Algebra (FractionRing S) F :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  let : IsScalarTower S (FractionRing S) F :=
    FractionRing.isScalarTower_liftAlgebra S F
  let : Algebra W F :=
    finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) qS
  let : IsScalarTower S W F :=
    localizationAtPrimeToExtension_isScalarTower
      (A := S) (K := FractionRing S) (L := F) qS
  let : IsScalarTower R W F := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap R F x = algebraMap S F (algebraMap R S x) :=
        IsScalarTower.algebraMap_apply R S F x
      _ = algebraMap W F (algebraMap S W (algebraMap R S x)) :=
        IsScalarTower.algebraMap_apply S W F (algebraMap R S x)
      _ = algebraMap W F (algebraMap R W x) := by
        rw [← IsScalarTower.algebraMap_apply R S W]
  let : IsScalarTower V W F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext pR.primeCompl
    ext x
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R V F,
      ← IsScalarTower.algebraMap_apply R V W,
      ← IsScalarTower.algebraMap_apply R W F]
  let : Algebra K₀ F :=
    fractionRingToExtensionAlgebra (V := V) (K := K) (L := F)
  let : IsScalarTower K₀ K F :=
    fractionRingToChosenFractionFieldToExtension_isScalarTower
      (V := V) (K := K) (L := F)
  let : IsScalarTower V K₀ F :=
    fractionRingToExtension_isScalarTower (V := V) (K := K) (L := F)
  let : Algebra Kroot F :=
    finiteExtensionAtPrimeFractionRingAlgebra (S := S) (D := D) qS
  let : IsScalarTower W Kroot F :=
    finiteExtensionAtPrime_literalFractionRingTower
      (S := S) (D := D) qS
  let : IsScalarTower V Kroot F := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap V F x =
      algebraMap Kroot F (algebraMap V Kroot x)
    calc
      algebraMap V F x = algebraMap W F (algebraMap V W x) :=
        IsScalarTower.algebraMap_apply V W F x
      _ = algebraMap Kroot F (algebraMap W Kroot (algebraMap V W x)) :=
        IsScalarTower.algebraMap_apply W Kroot F (algebraMap V W x)
      _ = algebraMap Kroot F (algebraMap V Kroot x) := by
        rw [IsScalarTower.algebraMap_apply V W Kroot]
  let : IsScalarTower K₀ Kroot F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors V)
    ext x
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply V K₀ F,
      ← IsScalarTower.algebraMap_apply V K₀ Kroot,
      ← IsScalarTower.algebraMap_apply V Kroot F]
  let : FiniteDimensional Kroot F :=
    finiteExtensionAtPrime_fractionRing_finiteDimensional
      (S := S) (D := D) qS
  let B := Localization.AtPrime qD
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B qD.primeCompl
      qD.primeCompl_le_nonZeroDivisors
  let : Algebra W B := finiteLiesOverLocalizationAlgebra qS qD
  let : Algebra B F :=
    finiteLiesOverLocalizationToFractionRingAlgebra qD
  let : IsFractionRing B F :=
    localizationAtPrimeToFractionField_isFractionRing (K := F) qD
  let : IsScalarTower W B F :=
    finiteLiesOverLocalization_fractionRingTower qS qD
  intro m hm
  exact
    integralClosure_selectedRootPrime_genericTensorTowerComponent_etale_of_ramification_dvd
      (R := R) (N := N) (p := p) hdimR hN
      (C := Cnorm) (L := L) hdiv hCharZeroV
      (K₁ := K) (B := B) (K' := F) m hm

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.ActiveRootFixedComponentEtale
import EtaleFundamentalGroups.Normalization.Localization.IntegralClosureAtPrimeEquiv

/-!
# Literal localized normalization for an active Galois root

This leaf converts the active-root normalization theorem to the literal
localized normalization used by special local purity.  Keeping the bridge in
its own compiled module avoids re-elaborating the completed chosen-component
construction inside every branch of a full-cover trichotomy.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- A chosen fraction field of a domain acts on any faithful field extension
through the literal fraction ring. -/
@[reducible]
noncomputable def chosenFractionFieldToFaithfulFieldAlgebra
    {R : Type uA} {K : Type uK} {F : Type uA}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [Algebra R F] [FaithfulSMul R F] : Algebra K F := by
  letI : Algebra (FractionRing R) F := FractionRing.liftAlgebra R F
  exact ((algebraMap (FractionRing R) F).comp
    (FractionRing.algEquiv R K).symm.toRingHom).toAlgebra

/-- The chosen action is compatible with the original domain map. -/
theorem chosenFractionFieldToFaithfulField_isScalarTower
    {R : Type uA} {K : Type uK} {F : Type uA}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [Algebra R F] [FaithfulSMul R F] :
    letI : Algebra K F :=
      chosenFractionFieldToFaithfulFieldAlgebra (R := R) (K := K) (F := F)
    IsScalarTower R K F := by
  let : Algebra K F :=
    chosenFractionFieldToFaithfulFieldAlgebra (R := R) (K := K) (F := F)
  let : Algebra (FractionRing R) F := FractionRing.liftAlgebra R F
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap R F x =
    algebraMap (FractionRing R) F
      ((FractionRing.algEquiv R K).symm (algebraMap R K x))
  rw [← (FractionRing.algEquiv R K).commutes x,
    (FractionRing.algEquiv R K).symm_apply_apply]
  exact IsScalarTower.algebraMap_apply R (FractionRing R) F x

/-- The active-root fixed-component theorem, expressed as the literal
localization of the normalization of the finite ambient ring. -/
theorem
    localization_integralClosure_strictNormalCrossingsGaloisActiveRoot_fixedComponent_etale
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
    let hp : Prime p := by
      rcases prime_or_isUnit_algebraMap_localizationAtPrime P
          (hNC.2.2.2.1 j hj) with hprime | hunit
      · exact hprime
      · have htCompl : t j ∈ P.primeCompl :=
          (IsLocalization.AtPrime.isUnit_to_map_iff
            (Localization.AtPrime P) P (t j)).mp hunit
        exact (htCompl htjP).elim
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
    ∀ {D : Type uA} [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
      [Algebra R D] [Algebra S D] [IsScalarTower R S D]
      [FaithfulSMul S D] [Module.Finite S D]
      (qD : Ideal D) [qD.IsPrime] [qD.LiesOver qS],
      let F := FractionRing D
      letI : FaithfulSMul R D := FaithfulSMul.trans R S D
      letI : FaithfulSMul R F := FaithfulSMul.trans R D F
      letI : Algebra K F :=
        chosenFractionFieldToFaithfulFieldAlgebra (R := R) (K := K) (F := F)
      letI : IsScalarTower R K F :=
        chosenFractionFieldToFaithfulField_isScalarTower
          (R := R) (K := K) (F := F)
      ∀ (m : Ideal (F ⊗[K] L)) (hm : m.IsMaximal),
        letI : m.IsMaximal := hm
        let M := GenericTensorFieldComponent m
        letI : Algebra D M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := D) m
        letI : SMul D M :=
          (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
        letI : IsScalarTower D F M :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        let Q := Localization.AtPrime qD
        letI : Algebra Q F :=
          localizationAtPrimeToFractionFieldAlgebra (K := F) qD
        letI : IsFractionRing Q F :=
          localizationAtPrimeToFractionField_isFractionRing (K := F) qD
        letI : Algebra Q M :=
          localizationAtPrimeToExtensionAlgebra (K := F) (L := M) qD
        letI : SMul Q M :=
          (localizationAtPrimeToExtensionAlgebra (K := F) (L := M) qD).toSMul
        letI : IsScalarTower Q F M :=
          localizationAtPrimeToFractionFieldToExtension_isScalarTower
            (K := F) (L := M) qD
        letI : IsScalarTower D Q M :=
          localizationAtPrimeToExtension_isScalarTower
            (K := F) (L := M) qD
        letI := integralClosureLocalizationAlgebra (L := M) qD
        Algebra.Etale Q
          (Localization (Algebra.algebraMapSubmonoid
            (integralClosure D M) qD.primeCompl)) := by
  dsimp only
  intro D _ _ _ _ _ _ _ _ qD _ _
  let R := Localization.AtPrime P
  let p : R := algebraMap A R (t j)
  let N := splitStrictNormalCrossingsGaloisRamificationIndex
    (K := K) (L := L) t hNC j
  have hN : 0 < N :=
    splitStrictNormalCrossingsGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC j
  let g : R[X] := X ^ N - C p
  let S := AdjoinRoot g
  let F := FractionRing D
  have hgeometryS :=
    splitStrictNormalCrossings_heightTwo_galoisSingleRootCover_geometry
      (K := K) (L := L) hNC j hj P hP htjP
  let : IsRegularLocalRing S := hgeometryS.1
  let : IsDomain S := hgeometryS.2.1
  let : Module.Free R S :=
    (Polynomial.monic_X_pow_sub_C p hN.ne').free_adjoinRoot
  let : FaithfulSMul R S := inferInstance
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : FaithfulSMul R D := FaithfulSMul.trans R S D
  let : FaithfulSMul R F := FaithfulSMul.trans R D F
  let : Algebra K F :=
    chosenFractionFieldToFaithfulFieldAlgebra (R := R) (K := K) (F := F)
  let : IsScalarTower R K F :=
    chosenFractionFieldToFaithfulField_isScalarTower
      (R := R) (K := K) (F := F)
  intro m hm
  let : m.IsMaximal := hm
  let M := GenericTensorFieldComponent m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D F M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Q := Localization.AtPrime qD
  let : Algebra Q F :=
    localizationAtPrimeToFractionFieldAlgebra (K := F) qD
  let : IsFractionRing Q F :=
    localizationAtPrimeToFractionField_isFractionRing (K := F) qD
  let : Algebra Q M :=
    localizationAtPrimeToExtensionAlgebra (K := F) (L := M) qD
  let : SMul Q M :=
    (localizationAtPrimeToExtensionAlgebra (K := F) (L := M) qD).toSMul
  let : IsScalarTower Q F M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := F) (L := M) qD
  let : IsScalarTower D Q M :=
    localizationAtPrimeToExtension_isScalarTower
      (K := F) (L := M) qD
  let : Algebra (integralClosure D M) (integralClosure Q M) :=
    integralClosureLocalizationAlgebra (L := M) qD
  have hlocal :=
    integralClosure_strictNormalCrossingsGaloisActiveRoot_fixedComponent_etale
      (K := K) (L := L) hNC j hj P hP htjP hCharZero
        (D := D) qD m hm
  exact localization_integralClosure_etale_of_local_integralClosure_etale
    (A := D) (K := F) (L := M) qD hlocal

end EtaleFundamentalGroups.Kummer

end

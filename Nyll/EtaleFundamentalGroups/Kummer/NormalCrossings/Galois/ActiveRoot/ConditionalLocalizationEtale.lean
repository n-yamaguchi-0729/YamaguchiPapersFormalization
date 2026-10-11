/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.ActiveRoot.LocalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCover

/-!
# A conditional active root in the exact Galois cover

For an active conditional stage, its exponent and radicand are the common
Galois branch index and the corresponding localized boundary parameter.
This leaf performs those two rewrites before specializing the active-root
fixed-component theorem, keeping the larger full-cover dispatcher small.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- A conditional active root, with its exponent and radicand sourced from
the exact Galois cover data, has the literal fixed-component localized
normalization supplied by the active-root theorem. -/
theorem
  localization_integralClosure_strictNormalCrossingsGaloisConditionalActiveRoot_fixedComponent_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {s r : ℕ} {f : A} {t : Fin (s + 2) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (s + 2))
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (sigma : Equiv.Perm (Fin (s + 1)))
    (k : Fin (s + 1))
    (hkActive : (i.succAbove (sigma k)).1 < r)
    (htkP : t (i.succAbove (sigma k)) ∈ P)
    (hCharZero : CharZero
      (A ⧸ Ideal.span ({t (i.succAbove (sigma k))} : Set A))) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let a : Fin (s + 1) → R := heightTwoConditionalOtherRadicand t i P sigma
    let g : R[X] := X ^ n k - C (a k)
    let S := AdjoinRoot g
    let qS := Ideal.span ({AdjoinRoot.root g} : Set S)
    letI : Algebra R K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI : IsFractionRing R K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) P
    ∀ {D : Type uA} [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
      [Algebra R D] [Algebra S D] [IsScalarTower R S D]
      [FaithfulSMul S D] [Module.Finite S D] [FaithfulSMul R D]
      (qD : Ideal D) [qD.IsPrime], qD.under S = qS →
      let F := FractionRing D
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
  let e := heightTwoOtherBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  let R := Localization.AtPrime P
  let n := heightTwoConditionalOtherExponent t i r P e sigma
  let a : Fin (s + 1) → R := heightTwoConditionalOtherRadicand t i P sigma
  let j : Fin (s + 2) := i.succAbove (sigma k)
  have hnkEq : n k =
      splitStrictNormalCrossingsGaloisRamificationIndex
        (K := K) (L := L) t hNC j := by
    simp [n, e, j, heightTwoConditionalOtherExponent,
      heightTwoOtherBranchGaloisRamificationIndex, hkActive, htkP]
  have hakEq : a k = algebraMap A R (t j) := by
    rfl
  dsimp only [n, e, j] at hnkEq
  dsimp only [a, j] at hakEq
  rw [hnkEq, hakEq]
  intro D _ _ _ _ _ _ _ _ _ qD _ hunder
  let g : R[X] :=
    X ^ splitStrictNormalCrossingsGaloisRamificationIndex
      (K := K) (L := L) t hNC j - C (algebraMap A R (t j))
  let S := AdjoinRoot g
  let qS := Ideal.span ({AdjoinRoot.root g} : Set S)
  have hgeometryS :=
    splitStrictNormalCrossings_heightTwo_galoisSingleRootCover_geometry
      (K := K) (L := L) hNC j hkActive P hP htkP
  let : IsRegularLocalRing S := hgeometryS.1
  let : IsDomain S := hgeometryS.2.1
  let : IsIntegrallyClosed S :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hgeometryS.2.2.1
  let : qS.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hgeometryS.2.2.2.1
  let : qD.LiesOver qS := ⟨hunder.symm⟩
  exact
    localization_integralClosure_strictNormalCrossingsGaloisActiveRoot_fixedComponent_etale
      (K := K) (L := L) hNC j hkActive P hP htkP hCharZero
        (D := D) qD

end EtaleFundamentalGroups.Kummer

end

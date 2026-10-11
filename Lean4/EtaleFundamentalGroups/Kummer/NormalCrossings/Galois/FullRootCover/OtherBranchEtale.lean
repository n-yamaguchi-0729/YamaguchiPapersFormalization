/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.ActualRootFirst.LocalizationEtale

/-!
# The active other branch of the exact Galois full cover

The actual-root-first construction is compiled in the preceding source leaf.
This module only installs the full-cover geometry and dispatches to it.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- At an active non-selected root prime of the exact Galois full cover, the
literal localized normalization in a fixed generic tensor component is
etale. -/
theorem
    localization_integralClosure_galoisFullRootCover_otherBranch_fixedComponent_etale
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
    (htiP : t i ∈ P)
    (sigma : Equiv.Perm (Fin (s + 1)))
    (k : Fin (s + 1))
    (hkActive : (i.succAbove (sigma k)).1 < r)
    (htkP : t (i.succAbove (sigma k)) ∈ P)
    (hCharZero : CharZero
      (A ⧸ Ideal.span ({t (i.succAbove (sigma k))} : Set A))) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let a : Fin (s + 1) → R := heightTwoConditionalOtherRadicand t i P sigma
    let B := iteratedRadical R (s + 1) n a
    let y : R := algebraMap A R (t i)
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    ∀ (hn : ∀ l, 0 < n l)
      (hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
        ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞)),
      letI : IsRegularLocalRing D := hgeometryD.1
      letI : IsDomain D := hgeometryD.2.1
      letI : IsIntegrallyClosed D :=
        SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
          hgeometryD.2.2
      letI : Algebra R K :=
        localizationAtPrimeToFractionFieldAlgebra (K := K) P
      letI : IsFractionRing R K :=
        localizationAtPrimeToFractionField_isFractionRing (K := K) P
      let K' := FractionRing D
      letI : Algebra K K' :=
        galoisFullRootCoverFractionFieldAlgebra n a hn N
          (heightTwoSelectedBranchGaloisRamificationIndex_pos
            (K := K) (L := L) t hNC i) y
      ∀ (m : Ideal (K' ⊗[K] L)) (hm : m.IsMaximal),
        letI : m.IsMaximal := hm
        let M := GenericTensorFieldComponent m
        letI : Algebra D M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := D) m
        letI : SMul D M :=
          (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
        letI : IsScalarTower D K' M :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        ∀ (q : Ideal D) [q.IsPrime], q.height = 1 →
          q.under B = Ideal.span
            ({iteratedRadicalRoot R n a k} : Set B) →
          let Q := Localization.AtPrime q
          letI : Algebra Q K' :=
            localizationAtPrimeToFractionFieldAlgebra (K := K') q
          letI : IsFractionRing Q K' :=
            localizationAtPrimeToFractionField_isFractionRing (K := K') q
          letI : Algebra Q M :=
            localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
          letI : SMul Q M :=
            (localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q).toSMul
          letI : IsScalarTower Q K' M :=
            localizationAtPrimeToFractionFieldToExtension_isScalarTower
              (K := K') (L := M) q
          letI : IsScalarTower D Q M :=
            localizationAtPrimeToExtension_isScalarTower
              (K := K') (L := M) q
          letI := integralClosureLocalizationAlgebra (L := M) q
          Algebra.Etale Q
            (Localization (Algebra.algebraMapSubmonoid
              (integralClosure D M) q.primeCompl)) := by
  intro e N R n a B y F D hn hgeometryD
  have hN : 0 < N :=
    splitStrictNormalCrossingsGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  have hRegularLocalD : IsRegularLocalRing D := hgeometryD.1
  have hDomainD : IsDomain D := hgeometryD.2.1
  have hIntegrallyClosedD : IsIntegrallyClosed D :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hgeometryD.2.2
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : Module.FaithfullyFlat R B := faithfullyFlat_iteratedRadical n a hn
  let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
  let : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective R B).nontrivial
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R B y)
  let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
  let : FaithfulSMul R D := FaithfulSMul.trans R B D
  let K' := FractionRing D
  let : FaithfulSMul R K' := FaithfulSMul.trans R D K'
  let : Algebra K K' :=
    galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
  let : IsScalarTower R K K' :=
    galoisFullRootCoverFractionField_isScalarTower n a hn N hN y
  intro K'_ m hm
  let M := GenericTensorFieldComponent m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro M' q hqPrime hqHeight hunderB
  let Q := Localization.AtPrime q
  let : Algebra Q K' :=
    localizationAtPrimeToFractionFieldAlgebra (K := K') q
  let : IsFractionRing Q K' :=
    localizationAtPrimeToFractionField_isFractionRing (K := K') q
  let : Algebra Q M :=
    localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
  let : SMul Q M :=
    (localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q).toSMul
  let : IsScalarTower Q K' M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K') (L := M) q
  let : IsScalarTower D Q M :=
    localizationAtPrimeToExtension_isScalarTower (K := K') (L := M) q
  let : Algebra (integralClosure D M) (integralClosure Q M) :=
    integralClosureLocalizationAlgebra (L := M) q
  exact
    @localization_integralClosure_galoisFullRootCover_actualRootFirst_fixedComponent_etale
      A K L _ _ _ _ _ _ _ _ _ _ _ _ _
        s r f t hNC i P (inferInstance : P.IsPrime) hP htiP sigma k
          hkActive htkP hCharZero hn hDomainD hIntegrallyClosedD q hqPrime
            hqHeight hunderB m hm

end EtaleFundamentalGroups.Kummer

end

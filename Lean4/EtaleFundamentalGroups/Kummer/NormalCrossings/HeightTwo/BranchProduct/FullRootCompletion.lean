/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.ChosenRoot.TensorComponentEtale
import EtaleFundamentalGroups.Kummer.SelectedRoot.PrimeParameterLocalization
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.BranchProductFullRootCover

/-!
# Completed chosen components along a height-two branch-product root cover

For a chosen normalization prime above one boundary branch, localization at
that branch produces the canonical finite DVR normalization used by the
completed actual-factor theorem.  Its ramification index divides the
branch-product exponent by construction.  We retain both the original prime
and its canonical localized prime, as well as the exact contraction of the
post-root tensor component to the completed component selected by that prime.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField

universe uA uC uK uL

/-- The exact source data returned by the completed chosen-root theorem.
Naming this proposition keeps strict-normal-crossings specializations from
re-elaborating the full completion and tensor tower in their public types. -/
def CompletedChosenRootTensorComponentEtaleAt
    {V : Type uA} {C : Type uC} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra K L] [IsScalarTower V K L]
    (Q : (IsLocalRing.maximalIdeal V).primesOver C)
    (pi : V)
    (hpi : IsLocalRing.maximalIdeal V = Ideal.span ({pi} : Set V))
    (N : ℕ) (hN : 0 < N) : Prop :=
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
  let varpiHat : Vhat :=
    standardDVRCompletionValuationSubringElement V K pi
  let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiHat)
  letI : IsDomain Rn :=
    completeDVFRootRing_isDomain H varpiHat
      (standardDVRCompletionValuationSubringElement_isUniformizer
        V K pi hpi) N hN
  let F := FractionRing Rn
  letI : Algebra Khat F :=
    completeDVFRootFractionFieldAlgebra H varpiHat
      (standardDVRCompletionValuationSubringElement_isUniformizer
        V K pi hpi) N hN
  letI : IsScalarTower Vhat Khat F :=
    completeDVFRootFractionField_isScalarTower H varpiHat
      (standardDVRCompletionValuationSubringElement_isUniformizer
        V K pi hpi) N hN
  letI : Algebra K F :=
    ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
  letI : IsScalarTower K Khat F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : FiniteDimensional Khat F :=
    pureRadicalFractionField_finiteDimensional hN varpiHat
      (completeDVFUniformizer_prime H varpiHat
        (standardDVRCompletionValuationSubringElement_isUniformizer
          V K pi hpi))
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let n := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  ∃ m : Ideal (F ⊗[K] L), ∃ hm : m.IsMaximal,
    letI : m.IsMaximal := hm
    let Pm := GenericTensorFieldComponent m
    letI : Algebra Rn Pm :=
      genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
    genericTensorTowerIntermediateIdeal
        (K := K) (F := Khat) (F' := F) (L := L) m = n ∧
      Algebra.Etale Rn (integralClosure Rn Pm)

/-- The chosen normalization prime on a strict-normal-crossings branch
selects a completed post-root component at the branch-product exponent.
The local prime and its ramification-index comparison with the original
prime are returned together with the exact tensor-component contraction. -/
theorem
    splitStrictNormalCrossings_branchProduct_completedChosenRootTensorComponent_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({t i} : Set A))]
    (hCharZero : CharZero (A ⧸ Ideal.span ({t i} : Set A))) :
    let N := heightTwoSelectedBranchRamificationProduct
      (K := K) (L := L) t hNC i
    let p := Ideal.span ({t i} : Set A)
    letI : p.IsPrime :=
      Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 i hi)
    let V := Localization.AtPrime p
    letI : IsDiscreteValuationRing V :=
      EtaleFundamentalGroups.isDiscreteValuationRing_localizationAtSpan_of_prime
        A (t i) (hNC.2.2.2.1 i hi)
    letI : Algebra V K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) p
    letI : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
    letI : IsScalarTower V K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) p
    letI : IsFractionRing V K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) p
    let C := integralClosure V L
    letI : IsFractionRing C L :=
      IsIntegralClosure.isFractionRing_of_finite_extension V K L C
    letI : IsDedekindDomain C :=
      IsIntegralClosure.isDedekindDomain V K L C
    letI : Module.IsTorsionFree V L :=
      Module.IsTorsionFree.trans_faithfulSMul V K L
    letI : Module.IsTorsionFree V C :=
      IsIntegralClosure.isTorsionFree V L
    letI : Module.Finite V C := IsIntegralClosure.finite V K L C
    let q := localizedNormalizationPrime (K := K) (L := L) p Q
    letI : q.IsMaximal :=
      localizedNormalizationPrime_isMaximal (K := K) (L := L) p Q
    letI : q.IsPrime := inferInstance
    letI : q.LiesOver (IsLocalRing.maximalIdeal V) :=
      localizedNormalizationPrime_liesOver (K := K) (L := L) p Q
    let qOver : (IsLocalRing.maximalIdeal V).primesOver C :=
      ⟨q, inferInstance, inferInstance⟩
    let piV : V := algebraMap A V (t i)
    let hpiV : IsLocalRing.maximalIdeal V =
        Ideal.span ({piV} : Set V) :=
      localizationAtPrime_maximalIdeal_eq_span_of_eq_span p (t i) rfl
    let hN : 0 < N :=
      heightTwoSelectedBranchRamificationProduct_pos
        (K := K) (L := L) t hNC i
    q.ramificationIdx V = Q.ramificationIdx A ∧
      CompletedChosenRootTensorComponentEtaleAt
        (V := V) (C := C) (K := K) (L := L)
        qOver piV hpiV N hN := by
  dsimp only
  classical
  let p := Ideal.span ({t i} : Set A)
  let : p.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime (hNC.2.2.2.1 i hi)
  let V := Localization.AtPrime p
  let : IsDiscreteValuationRing V :=
    EtaleFundamentalGroups.isDiscreteValuationRing_localizationAtSpan_of_prime
      A (t i) (hNC.2.2.2.1 i hi)
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) p
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) p
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p
  let C := integralClosure V L
  let : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L C
  let : IsDedekindDomain C :=
    IsIntegralClosure.isDedekindDomain V K L C
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.IsTorsionFree V C :=
    IsIntegralClosure.isTorsionFree V L
  let : Module.Finite V C := IsIntegralClosure.finite V K L C
  let q := localizedNormalizationPrime (K := K) (L := L) p Q
  let : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) p Q
  let : q.IsPrime := inferInstance
  let : q.LiesOver (IsLocalRing.maximalIdeal V) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) p Q
  let qOver : (IsLocalRing.maximalIdeal V).primesOver C :=
    ⟨q, inferInstance, inferInstance⟩
  let piV : V := algebraMap A V (t i)
  let N := heightTwoSelectedBranchRamificationProduct
    (K := K) (L := L) t hNC i
  have hram : q.ramificationIdx V = Q.ramificationIdx A :=
    localizedNormalizationPrime_ramificationIdx
      (K := K) (L := L) p Q
  refine ⟨hram, ?_⟩
  have hpiV : IsLocalRing.maximalIdeal V =
      Ideal.span ({piV} : Set V) :=
    localizationAtPrime_maximalIdeal_eq_span_of_eq_span p (t i) rfl
  have hN : 0 < N :=
    heightTwoSelectedBranchRamificationProduct_pos
      (K := K) (L := L) t hNC i
  have hdivGlobal : Q.ramificationIdx A ∣ N :=
    normalizationPrime_ramificationIdx_dvd_splitStrictNormalCrossingsProduct
      (K := K) (L := L) t hNC i hi Q
  have hdivLocal : qOver.1.ramificationIdx V ∣ N := by
    change q.ramificationIdx V ∣ N
    rw [hram]
    exact hdivGlobal
  let : CharZero (V ⧸ Ideal.span ({piV} : Set V)) :=
    charZero_quotient_algebraMap_localizationAtPrime p
      (hNC.2.2.2.1 i hi) (Ideal.mem_span_singleton_self (t i)) hCharZero
  have hCharZeroV : CharZero (V ⧸ IsLocalRing.maximalIdeal V) := by
    rw [hpiV]
    infer_instance
  exact integralClosure_completedChosenRootTensorComponent_etale
    (V := V) (C := C) (K := K) (L := L)
    qOver piV hpiV N hN hdivLocal hCharZeroV

end EtaleFundamentalGroups.Kummer

end

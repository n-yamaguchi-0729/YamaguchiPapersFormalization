/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Chosen.GenericComponentTarget
import EtaleFundamentalGroups.Completions.GenericTensor.ChosenIdealExhaustive
import EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorTowerIntermediate
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Completion

/-!
# Completed root tensor products at a common ramification exponent

Every component of the completed generic tensor product comes from a prime
of the original finite DVR extension.  If all of their ramification indices
divide one positive exponent, the prescribed-root actual-factor theorem
therefore applies componentwise.  The canonical Artinian product
decomposition then gives etaleness of the normalization in the original
post-root tensor product.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uV uC uK uL

variable {V : Type uV} {C : Type uC}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [CommRing C] [IsDedekindDomain C]
variable [Algebra V C] [Algebra.IsIntegral V C]
variable [Module.IsTorsionFree V C] [Module.Finite V C]
variable {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
variable {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
variable [Algebra V L] [IsScalarTower V C L]
variable [Algebra K L] [IsScalarTower V K L]

/-- If every branch index of the finite DVR extension divides `N`, the
normalization of every completed post-root tensor component is etale over
the `N`-th uniformizer-root ring. -/
theorem integralClosure_completedRootTensorComponent_etale_of_ramification_dvd
    (pi : V)
    (hpi : IsLocalRing.maximalIdeal V = Ideal.span ({pi} : Set V))
    (N : ℕ) (hN : 0 < N)
    (hdiv : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver C,
      Q.1.ramificationIdx V ∣ N)
    (hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V)) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
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
    letI : Algebra K F :=
      ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
    ∀ (m : Ideal (F ⊗[K] L)) (hm : m.IsMaximal),
      letI : m.IsMaximal := hm
      let P := GenericTensorFieldComponent m
      letI : Algebra Rn P :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
      Algebra.Etale Rn (integralClosure Rn P) := by
  dsimp only
  classical
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : IsLocalHom (algebraMap V Vhat) :=
    standardDVRToCompletion_isLocalHom V K
  let : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat
      (V := V) (K := K)
  let : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
  let : Module K Khat := (standardDVFCompletionAlgebra V K).toModule
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  let : Module V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toModule
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let varpiHat : Vhat :=
    standardDVRCompletionValuationSubringElement V K pi
  have hvarpiHat : H.valuation.IsUniformizer (varpiHat : Khat) :=
    standardDVRCompletionValuationSubringElement_isUniformizer V K pi hpi
  let : CharZero H.residueField :=
    charZero_standardDVFCompletionCompleteDVF_residueField V K hCharZero
  let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiHat)
  let : IsDomain Rn :=
    completeDVFRootRing_isDomain H varpiHat hvarpiHat N hN
  let F := FractionRing Rn
  let : Algebra Khat F :=
    completeDVFRootFractionFieldAlgebra H varpiHat hvarpiHat N hN
  let : IsScalarTower Vhat Khat F :=
    completeDVFRootFractionField_isScalarTower H varpiHat hvarpiHat N hN
  let : Algebra K F :=
    ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
  let : IsScalarTower K Khat F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : FiniteDimensional Khat F :=
    pureRadicalFractionField_finiteDimensional hN varpiHat
      (completeDVFUniformizer_prime H varpiHat hvarpiHat)
  intro m hm
  let : m.IsMaximal := hm
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := Khat) (F' := F) (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := Khat) (F' := F) (L := L) m
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  have hExhaustive :
      ∃ Q : (IsLocalRing.maximalIdeal V).primesOver C,
        completedGenericTensorChosenIdeal
          (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
          hmax hres Q.1 = n := by
    exact exists_completedGenericTensorChosenIdeal_eq
      (V := V) (C := C) (K := K) (L := L) n inferInstance
  obtain ⟨Q, hQ⟩ := hExhaustive
  let nQ := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  have hnQmax : nQ.IsMaximal :=
    completedGenericTensorChosenIdeal_isMaximal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
  have hTarget :
      ∃ target : CompleteDVF.{_, 0} (GenericTensorFieldComponent nQ),
        ∃ hExt : H.valuation.HasExtension target.valuation,
          letI : H.valuation.HasExtension target.valuation := hExt
          Module.Finite Vhat target.valuationSubring ∧
            ramificationIndex H.toDVF target.toDVF =
              Q.1.ramificationIdx V := by
    exact exists_completedChosenGenericComponent_completeDVF
      (V := V) (C := C) (K := K) (L := L) Q
  obtain ⟨target, hExt, hfinite, hram⟩ := hTarget
  let : H.valuation.HasExtension target.valuation := hExt
  let : Module.Finite Vhat target.valuationSubring := hfinite
  have hdivTarget : ramificationIndex H.toDVF target.toDVF ∣ N := by
    rw [hram]
    exact hdiv Q
  exact
    integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_intermediateIdeal_eq
      H varpiHat hvarpiHat N hN m hm nQ hnQmax hQ.symm target hdivTarget

/-- The componentwise theorem aggregated through the canonical Artinian
product decomposition of the completed generic tensor product. -/
theorem integralClosure_completedRootTensorProduct_etale_of_ramification_dvd
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pi : V)
    (hpi : IsLocalRing.maximalIdeal V = Ideal.span ({pi} : Set V))
    (N : ℕ) (hN : 0 < N)
    (hdiv : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver C,
      Q.1.ramificationIdx V ∣ N)
    (hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V)) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
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
    letI : Algebra K F :=
      ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
    let G := F ⊗[K] L
    letI : Algebra Rn G :=
      genericTensorProductLeftScalarAlgebra
        (R := Rn) (K := K) (F := F) (L := L)
    Algebra.Etale Rn (integralClosure Rn G) := by
  dsimp only
  classical
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : IsLocalHom (algebraMap V Vhat) :=
    standardDVRToCompletion_isLocalHom V K
  let : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat
      (V := V) (K := K)
  let : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
  let : Module K Khat := (standardDVFCompletionAlgebra V K).toModule
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  let : Module V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toModule
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let varpiHat : Vhat :=
    standardDVRCompletionValuationSubringElement V K pi
  have hvarpiHat : H.valuation.IsUniformizer (varpiHat : Khat) :=
    standardDVRCompletionValuationSubringElement_isUniformizer V K pi hpi
  let : CharZero H.residueField :=
    charZero_standardDVFCompletionCompleteDVF_residueField V K hCharZero
  let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiHat)
  let : IsDomain Rn :=
    completeDVFRootRing_isDomain H varpiHat hvarpiHat N hN
  let F := FractionRing Rn
  let : Algebra Khat F :=
    completeDVFRootFractionFieldAlgebra H varpiHat hvarpiHat N hN
  let : IsScalarTower Vhat Khat F :=
    completeDVFRootFractionField_isScalarTower H varpiHat hvarpiHat N hN
  let : Algebra K F :=
    ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
  let : IsScalarTower K Khat F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : FiniteDimensional Khat F :=
    pureRadicalFractionField_finiteDimensional hN varpiHat
      (completeDVFUniformizer_prime H varpiHat hvarpiHat)
  let G := F ⊗[K] L
  let : Algebra Rn G :=
    genericTensorProductLeftScalarAlgebra
      (R := Rn) (K := K) (F := F) (L := L)
  apply integralClosure_genericTensorProduct_etale
  intro m hm
  exact integralClosure_completedRootTensorComponent_etale_of_ramification_dvd
    (V := V) (C := C) (K := K) (L := L)
    pi hpi N hN hdiv hCharZero m hm

end EtaleFundamentalGroups.Kummer

end

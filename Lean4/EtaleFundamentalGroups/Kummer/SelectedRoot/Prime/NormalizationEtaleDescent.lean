/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.DVR.IntegralExtensionEtaleDescent
import EtaleFundamentalGroups.Kummer.Completions.RootTensor.EtalePrescribedExponent
import EtaleFundamentalGroups.Kummer.GenericTensor.Refinement.NormalizationLocal
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Completion
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtale
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletionField
import EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoRegularRing
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Etale descent at the selected root prime

For a fixed component of the generic tensor product after adjoining an
`N`-th root of a DVR uniformizer, every completed normalization factor is
identified with a refined component of the completed root tensor product.
The prescribed-exponent component theorem makes those factors etale, and
faithfully flat completion descends etaleness to the selected root DVR.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uR uC uL uB uF

local instance spanSingletonIsPrime
    {R : Type uR} [CommRing R] [IsDomain R]
    {p : R} [hp : Fact (Prime p)] :
    (Ideal.span ({p} : Set R)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime hp.out

/-- The selected-root completion algebra uses the literal right tensor inclusion.
This computation is checked before entering the larger descent proof. -/
private theorem selectedRootCompletion_algebraMap
    {R : Type uR} [CommRing R] [IsDomain R] [IsRegularRing R]
    {N : ℕ} (hN : 0 < N) {p : R} (hp : Prime p) :
    let P := Ideal.span ({p} : Set R)
    let D := AdjoinRoot (X ^ N - C p)
    let q := Ideal.span
      ({AdjoinRoot.root (X ^ N - C p)} : Set D)
    let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
      (prime_adjoinRoot_root_of_prime hN hp)
    let V := Localization.AtPrime P
    let : IsDiscreteValuationRing V :=
      EtaleFundamentalGroups.isDiscreteValuationRing_localizationAtSpan_of_prime
        R p hp
    let K := FractionRing V
    let Vhat := standardDVFCompletionValuationSubring V K
    let : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    let pV := algebraMap R V p
    let pHat := standardDVRCompletionValuationSubringElement V K pV
    let Rhat := AdjoinRoot (X ^ N - C pHat)
    let : q.LiesOver P := span_root_liesOver_span_radicand hN hp
    let : Algebra V (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver P q
    let : Algebra (Localization.AtPrime q) Rhat :=
      adjoinRootLocalizationAtRootPrimeCompletionAlgebra hN hp
    ∀ w : Localization.AtPrime q,
      adjoinRootLocalizationAtRootPrimeCompletionAlgEquiv hN hp
          ((Algebra.TensorProduct.includeRight :
            Localization.AtPrime q →ₐ[V] Vhat ⊗[V] Localization.AtPrime q) w) =
        algebraMap (Localization.AtPrime q) Rhat w := by
  intro P D q hP hq V hV K Vhat aVVhat pV pHat Rhat hqP aVW aWRhat w
  rfl

/-- A finite separable normalization is etale when all its standard completed
local factors are etale. The normalization properties needed to form those
factors are constructed here, before the supplied factor proof is applied. -/
private theorem integralClosure_etale_of_completedFactors
    (W : Type uR) (K : Type uC) (M : Type uL)
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field K] [Algebra W K] [IsFractionRing W K]
    [Field M] [Algebra K M] [Algebra W M] [IsScalarTower W K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (hlocal :
      let Croot := integralClosure W M
      ∀ [IsFractionRing Croot M] [IsDedekindDomain Croot]
        [Module.IsTorsionFree W Croot] [Module.Finite W Croot],
      let pRoot := IsLocalRing.maximalIdeal W
      let Hw := standardDVFCompletionCompleteDVF W K
      let What := Hw.valuationSubring
      let Aroot := fun Q : pRoot.primesOver Croot =>
        completedPrimeValuationSubring (L := M) Q
      let : Algebra W What := standardDVFCompletionValuationSubringAlgebra W K
      let : ∀ Q, Algebra What (Aroot Q) := fun Q =>
        completedPrimeValuationSubringCompletionAlgebra
          (V := W) (C := Croot) (K := K) (L := M) Q
      ∀ Q, Algebra.Etale What (Aroot Q)) :
    Algebra.Etale W (integralClosure W M) := by
  let Croot := integralClosure W M
  let : IsFractionRing Croot M :=
    IsIntegralClosure.isFractionRing_of_finite_extension W K M Croot
  let : IsDedekindDomain Croot :=
    IsIntegralClosure.isDedekindDomain W K M Croot
  let : Module.IsTorsionFree W M := by
    let : Module.IsTorsionFree K M :=
      DivisionSemiring.to_moduleIsTorsionFree (𝕜 := K) (M := M)
    exact Module.IsTorsionFree.trans_faithfulSMul W K M
  let : Module.IsTorsionFree W Croot := IsIntegralClosure.isTorsionFree W M
  let : Module.Finite W Croot := IsIntegralClosure.finite W K M Croot
  exact etale_of_completedPrimeValuationSubring_etale
    (V := W) (C := Croot) (K := K) (L := M) hlocal

/-- Transport completed tensor components along an equivalence of the completed
base rings, and descend their normalization etaleness to the original DVR.
The fraction-field lift, chosen component, and compatible quotient map are
constructed here from the given base equivalence. -/
private theorem integralClosure_etale_of_completedTensorTransport
    (W : Type uR) (K : Type uC) (M : Type uL)
    (Rhat : Type uB) (Fhat : Type uF)
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field K] [Algebra W K] [IsFractionRing W K]
    [Field M] [Algebra K M] [Algebra W M] [IsScalarTower W K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [CommRing Rhat] [Algebra W Rhat]
    [Field Fhat] [Algebra Rhat Fhat] [IsFractionRing Rhat Fhat]
    [Algebra W Fhat] [IsScalarTower W Rhat Fhat]
    [Algebra K Fhat] [IsScalarTower W K Fhat]
    (eBase :
      let Hw := standardDVFCompletionCompleteDVF W K
      let What := Hw.valuationSubring
      let : Algebra W What := standardDVFCompletionValuationSubringAlgebra W K
      What ≃ₐ[W] Rhat)
    (hlocal : ∀ (qF : Ideal (Fhat ⊗[K] M)) [qF.IsMaximal],
      let : Algebra Rhat (GenericTensorFieldComponent qF) :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) qF
      Algebra.Etale Rhat (integralClosure Rhat (GenericTensorFieldComponent qF))) :
    Algebra.Etale W (integralClosure W M) := by
  classical
  apply integralClosure_etale_of_completedFactors W K M
  intro Croot hCrootFraction hCrootDedekind hCrootTorsion hCrootFinite
    pRoot Hw What Aroot wWhatAlgebra completedAlgebras Qroot
  let Lhat := standardDVFCompletionField W K
  let : IsLocalHom (R := W) (S := What) (F := W →+* What)
      (algebraMap W What) :=
    standardDVRToCompletion_isLocalHom W K
  let : Module.FaithfullyFlat W What :=
    standardDVRCompletionValuationSubring_faithfullyFlat (V := W) (K := K)
  let kLhatAlgebra : Algebra K Lhat := standardDVFCompletionAlgebra W K
  let wLhatAlgebra : Algebra W Lhat :=
    standardDVFCompletionBaseAlgebra (V := W) (K := K)
  let : SMul K Lhat := kLhatAlgebra.toSMul
  let : Module K Lhat := kLhatAlgebra.toModule
  let : SMul W Lhat := wLhatAlgebra.toSMul
  let : Module W Lhat := wLhatAlgebra.toModule
  let : IsScalarTower W K Lhat :=
    standardDVFCompletion_isScalarTower (V := W) (K := K)
  let whatLhatAlgebra : Algebra What Lhat :=
    Algebra.ofSubsemiring Hw.valuation.valuationSubring
  let : SMul What Lhat := whatLhatAlgebra.toSMul
  let : IsScalarTower W What Lhat :=
    standardDVRCompletionValuationSubring_isScalarTower (V := W) (K := K)
  let hmaxW : (IsLocalRing.maximalIdeal W).map (algebraMap W What) =
      IsLocalRing.maximalIdeal What :=
    standardDVRToCompletion_maximalIdeal_map_eq W K
  let hresW : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap W What)) :=
    standardDVRToCompletion_residueFieldMap_bijective W K
  let qstd : Ideal (Lhat ⊗[K] M) := completedGenericTensorChosenIdeal
    (R := W) (R' := What) (C := Croot) (K := K) (L := M)
    (K' := Lhat) hmaxW hresW Qroot.1
  let : qstd.IsMaximal :=
    completedGenericTensorChosenIdeal_isMaximal
      (R := W) (R' := What) (C := Croot) (K := K) (L := M)
      (K' := Lhat) hmaxW hresW Qroot.1
  let hFrac : IsFractionRing What Lhat :=
    Hw.toDVF.valuationSubring_isFractionRing
  let eField : Lhat ≃ₐ[K] Fhat :=
    IsFractionRing.fieldEquivOfAlgEquiv K Lhat Fhat eBase
  let : IsScalarTower K K Lhat :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K K Fhat :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let eTensor : (Lhat ⊗[K] M) ≃ₐ[K] (Fhat ⊗[K] M) :=
    Algebra.TensorProduct.congr eField (AlgEquiv.refl : M ≃ₐ[K] M)
  let qF : Ideal (Fhat ⊗[K] M) := qstd.map eTensor.toRingEquiv
  let : qF.IsMaximal :=
    (inferInstance : qstd.IsMaximal).map_bijective
      (f := eTensor.toRingEquiv) eTensor.bijective
  let eQuot : GenericTensorFieldComponent qstd ≃ₐ[K]
      GenericTensorFieldComponent qF :=
    Ideal.quotientEquivAlg qstd qF eTensor rfl
  let Pstd := GenericTensorFieldComponent qstd
  let PqF := GenericTensorFieldComponent qF
  let : Algebra Rhat PqF :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) qF
  have hRoot : Algebra.Etale Rhat (integralClosure Rhat PqF) := hlocal qF
  have heQuot (z : Lhat) :
      eQuot (algebraMap Lhat Pstd z) =
        algebraMap Fhat PqF (eField z) := by
    change Ideal.Quotient.mk qF
        (eTensor ((Algebra.TensorProduct.includeLeft :
          Lhat →ₐ[K] Lhat ⊗[K] M) z)) =
      Ideal.Quotient.mk qF
        ((Algebra.TensorProduct.includeLeft :
          Fhat →ₐ[K] Fhat ⊗[K] M) (eField z))
    apply congrArg (Ideal.Quotient.mk qF)
    change (Algebra.TensorProduct.congr eField
        (AlgEquiv.refl : M ≃ₐ[K] M)) (z ⊗ₜ[K] (1 : M)) =
      eField z ⊗ₜ[K] (1 : M)
    exact Algebra.TensorProduct.map_tmul
      (eField : Lhat →ₐ[K] Fhat) (AlgHom.id K M) z 1
  have hcompat : eQuot.toRingEquiv.toRingHom.comp (algebraMap What Pstd) =
      (algebraMap Rhat PqF).comp eBase.toRingEquiv.toRingHom := by
    apply RingHom.ext
    intro x
    change eQuot (algebraMap What Pstd x) = algebraMap Rhat PqF (eBase x)
    calc
      eQuot (algebraMap What Pstd x) =
          algebraMap Fhat PqF (eField (algebraMap What Lhat x)) :=
        heQuot (algebraMap What Lhat x)
      _ = algebraMap Fhat PqF (algebraMap Rhat Fhat (eBase x)) :=
        congrArg (algebraMap Fhat PqF)
          (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K Lhat Fhat eBase x)
      _ = algebraMap Rhat PqF (eBase x) := rfl
  have hStd : Algebra.Etale What (integralClosure What Pstd) :=
    integralClosure_etale_of_baseAndAmbientEquiv
      eBase.toRingEquiv eQuot.toRingEquiv hcompat hRoot
  let eChosen : integralClosure What Pstd ≃ₐ[What] Aroot Qroot :=
    completedGenericTensorChosenIntegralClosureAlgEquiv
      (V := W) (C := Croot) (K := K) (L := M) Qroot
  exact Algebra.Etale.of_equiv eChosen

/-- If every ramification index over the original DVR divides `N`, then the
normalization of the selected-root DVR in every fixed post-root generic
tensor component is etale. -/
theorem integralClosure_selectedRootPrime_genericTensorComponent_etale_of_ramification_dvd
    {R : Type uR} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    {N : ℕ} (hN : 0 < N) {p : R} [hp : Fact (Prime p)]
    {C : Type uC} [CommRing C] [IsDedekindDomain C]
    [Algebra (Localization.AtPrime (Ideal.span ({p} : Set R))) C]
    [Algebra.IsIntegral (Localization.AtPrime (Ideal.span ({p} : Set R))) C]
    [Module.IsTorsionFree (Localization.AtPrime (Ideal.span ({p} : Set R))) C]
    [Module.Finite (Localization.AtPrime (Ideal.span ({p} : Set R))) C]
    {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra (Localization.AtPrime (Ideal.span ({p} : Set R))) L]
    [IsScalarTower (Localization.AtPrime (Ideal.span ({p} : Set R))) C L]
    [Algebra (FractionRing (Localization.AtPrime
      (Ideal.span ({p} : Set R)))) L]
    [IsScalarTower (Localization.AtPrime (Ideal.span ({p} : Set R)))
      (FractionRing (Localization.AtPrime (Ideal.span ({p} : Set R)))) L]
    [FiniteDimensional
      (FractionRing (Localization.AtPrime (Ideal.span ({p} : Set R)))) L]
    [Algebra.IsSeparable
      (FractionRing (Localization.AtPrime (Ideal.span ({p} : Set R)))) L]
    (hdiv : ∀ Q : (IsLocalRing.maximalIdeal
        (Localization.AtPrime (Ideal.span ({p} : Set R)))).primesOver C,
      Q.1.ramificationIdx
        (Localization.AtPrime (Ideal.span ({p} : Set R))) ∣ N)
    (hCharZero : CharZero
      (Localization.AtPrime (Ideal.span ({p} : Set R)) ⧸
        IsLocalRing.maximalIdeal
          (Localization.AtPrime (Ideal.span ({p} : Set R))))) :
    let : IsRegularRing R :=
      EtaleFundamentalGroups.isRegularRing_of_isRegularLocalRing_dimension_two hdim
    let P := Ideal.span ({p} : Set R)
    let D := AdjoinRoot (X ^ N - Polynomial.C p)
    let q := Ideal.span
      ({AdjoinRoot.root (X ^ N - Polynomial.C p)} : Set D)
    let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp.out
    let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
      (prime_adjoinRoot_root_of_prime hN hp.out)
    let : q.LiesOver P := span_root_liesOver_span_radicand hN hp.out
    let V := Localization.AtPrime P
    let : IsDiscreteValuationRing V :=
      EtaleFundamentalGroups.isDiscreteValuationRing_localizationAtSpan_of_prime
        R p hp.out
    let K := FractionRing V
    let pV := algebraMap R V p
    let Rn := AdjoinRoot (X ^ N - Polynomial.C pV)
    let W := Localization.AtPrime q
    let : Algebra V W := Localization.AtPrime.algebraOfLiesOver P q
    let : IsDomain W := adjoinRootLocalizationAtRootPrime_isDomain hN hp.out
    let : IsDiscreteValuationRing W :=
      adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing hN hp.out
    let eLocal : Rn ≃ₐ[V] W :=
      adjoinRootLocalizationAtRootPrimeAlgEquiv hN hp.out
    let : Module.Free V Rn :=
      (Polynomial.monic_X_pow_sub_C pV hN.ne').free_adjoinRoot
    let : Module.Free V W := Module.Free.of_equiv eLocal.toLinearEquiv
    let Kroot := FractionRing W
    let : FaithfulSMul V W := inferInstance
    let : FaithfulSMul V Kroot := FaithfulSMul.trans V W Kroot
    let : Algebra K Kroot := FractionRing.liftAlgebra V Kroot
    ∀ (m : Ideal (Kroot ⊗[K] L)) (hm : m.IsMaximal),
      let : m.IsMaximal := hm
      let M := GenericTensorFieldComponent m
      let : Algebra W M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := W) m
      Algebra.Etale W (integralClosure W M) := by
  classical
  intro hRegular P D q hP hq hqP V hV K pV Rn W aVW hDomainW hDvrW eLocal
    hFreeRn hFreeW Kroot hFaithVW hFaithVKroot aKKroot
  let : IsScalarTower V K Kroot :=
    FractionRing.isScalarTower_liftAlgebra V Kroot
  intro m hm hmInstance M wMAlgebra
  let : SMul W M := wMAlgebra.toSMul
  let : Module W M := wMAlgebra.toModule
  let : IsScalarTower W Kroot M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
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
  let kKhatAlgebra : Algebra K Khat := standardDVFCompletionAlgebra V K
  let vKhatAlgebra : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := kKhatAlgebra.toSMul
  let : Module K Khat := kKhatAlgebra.toModule
  let : SMul V Khat :=
    vKhatAlgebra.toSMul
  let : Module V Khat :=
    vKhatAlgebra.toModule
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : SMul Vhat Khat :=
    (Algebra.ofSubsemiring H.valuation.valuationSubring).toSMul
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  have hpiV : IsLocalRing.maximalIdeal V =
      Ideal.span ({pV} : Set V) :=
    localizationAtPrime_maximalIdeal_eq_span_of_eq_span P p rfl
  let pHat := standardDVRCompletionValuationSubringElement V K pV
  have hpHat : H.valuation.IsUniformizer (pHat : Khat) :=
    standardDVRCompletionValuationSubringElement_isUniformizer
      V K pV hpiV
  let Rhat := AdjoinRoot (X ^ N - Polynomial.C pHat)
  let : IsDomain Rhat :=
    completeDVFRootRing_isDomain H pHat hpHat N hN
  let Fhat := FractionRing Rhat
  let khatFhatAlgebra : Algebra Khat Fhat :=
    completeDVFRootFractionFieldAlgebra H pHat hpHat N hN
  let : SMul Khat Fhat := khatFhatAlgebra.toSMul
  let : IsScalarTower Vhat Khat Fhat :=
    completeDVFRootFractionField_isScalarTower H pHat hpHat N hN
  let kFhatAlgebra : Algebra K Fhat :=
    ((algebraMap Khat Fhat).comp (algebraMap K Khat)).toAlgebra
  let : SMul K Fhat := kFhatAlgebra.toSMul
  let : IsScalarTower K Khat Fhat :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := Khat) (A := Fhat)
      (fun _x : K => rfl)
  let : FiniteDimensional Khat Fhat :=
    pureRadicalFractionField_finiteDimensional hN pHat
      (completeDVFUniformizer_prime H pHat hpHat)
  let : Algebra W Rhat :=
    adjoinRootLocalizationAtRootPrimeCompletionAlgebra hN hp.out
  let : Module.FaithfullyFlat W Rhat :=
    adjoinRootLocalizationAtRootPrimeCompletion_faithfullyFlat hN hp.out
  let : FaithfulSMul W Rhat :=
    Module.FaithfullyFlat.faithfulSMul
  let : FaithfulSMul W Fhat := FaithfulSMul.trans W Rhat Fhat
  let krootFhatAlgebra : Algebra Kroot Fhat := FractionRing.liftAlgebra W Fhat
  let : SMul Kroot Fhat := krootFhatAlgebra.toSMul
  let : IsScalarTower W Kroot Fhat :=
    FractionRing.isScalarTower_liftAlgebra W Fhat
  let : IsScalarTower K Kroot Fhat := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    have hMaps : algebraMap K Fhat =
        (algebraMap Kroot Fhat).comp (algebraMap K Kroot) := by
      apply IsFractionRing.ringHom_ext (A := V)
      intro v
      change algebraMap Khat Fhat
          (algebraMap K Khat (algebraMap V K v)) =
        algebraMap Kroot Fhat
          (algebraMap K Kroot (algebraMap V K v))
      have hLeft :
          algebraMap Khat Fhat (algebraMap K Khat (algebraMap V K v)) =
            algebraMap Rhat Fhat
              (algebraMap Vhat Rhat (algebraMap V Vhat v)) := by
        calc
          _ = algebraMap Khat Fhat (algebraMap V Khat v) :=
            congrArg (algebraMap Khat Fhat)
              (IsScalarTower.algebraMap_apply V K Khat v).symm
          _ = algebraMap Khat Fhat
                (algebraMap Vhat Khat (algebraMap V Vhat v)) :=
            congrArg (algebraMap Khat Fhat)
              (IsScalarTower.algebraMap_apply V Vhat Khat v)
          _ = algebraMap Vhat Fhat (algebraMap V Vhat v) :=
            (IsScalarTower.algebraMap_apply Vhat Khat Fhat _).symm
          _ = algebraMap Rhat Fhat
                (algebraMap Vhat Rhat (algebraMap V Vhat v)) :=
            IsScalarTower.algebraMap_apply Vhat Rhat Fhat _
      have hRight :
          algebraMap Kroot Fhat (algebraMap K Kroot (algebraMap V K v)) =
            algebraMap Rhat Fhat
              (algebraMap W Rhat (algebraMap V W v)) := by
        calc
          _ = algebraMap Kroot Fhat (algebraMap V Kroot v) :=
            congrArg (algebraMap Kroot Fhat)
              (IsScalarTower.algebraMap_apply V K Kroot v).symm
          _ = algebraMap Kroot Fhat
                (algebraMap W Kroot (algebraMap V W v)) :=
            congrArg (algebraMap Kroot Fhat)
              (IsScalarTower.algebraMap_apply V W Kroot v)
          _ = algebraMap W Fhat (algebraMap V W v) :=
            (IsScalarTower.algebraMap_apply W Kroot Fhat _).symm
          _ = algebraMap Rhat Fhat
                (algebraMap W Rhat (algebraMap V W v)) :=
            IsScalarTower.algebraMap_apply W Rhat Fhat _
      let T := Vhat ⊗[V] W
      let inLeft : Vhat →ₐ[V] T := Algebra.TensorProduct.includeLeft
      let inRight : W →ₐ[V] T := Algebra.TensorProduct.includeRight
      let eCompletion : T ≃ₐ[Vhat] Rhat :=
        adjoinRootLocalizationAtRootPrimeCompletionAlgEquiv hN hp.out
      have hVRhat :
          algebraMap Vhat Rhat (algebraMap V Vhat v) =
            algebraMap W Rhat (algebraMap V W v) := by
        calc
          algebraMap Vhat Rhat (algebraMap V Vhat v) =
              eCompletion (inLeft (algebraMap V Vhat v)) :=
            (eCompletion.commutes _).symm
          _ = eCompletion (inRight (algebraMap V W v)) :=
            congrArg eCompletion ((inLeft.commutes v).trans (inRight.commutes v).symm)
          _ = algebraMap W Rhat (algebraMap V W v) :=
            selectedRootCompletion_algebraMap (R := R) hN hp.out (algebraMap V W v)
      exact hLeft.trans ((congrArg (algebraMap Rhat Fhat) hVRhat).trans hRight.symm)
    exact DFunLike.congr_fun hMaps x
  apply integralClosure_etale_of_completedTensorTransport W Kroot M Rhat Fhat
    (adjoinRootLocalizationAtRootPrimeStandardCompletionAlgEquiv hN hp.out)
  intro qF hqF rhatPqFAlgebra
  let n : Ideal (Fhat ⊗[K] L) := genericTensorRefineChosenComponentIdeal
    (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  let : n.IsMaximal :=
    genericTensorRefineChosenComponentIdeal_isMaximal
      (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  let Pn := GenericTensorFieldComponent n
  let : Algebra Rhat Pn :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Rhat) n
  have hRoot : Algebra.Etale Rhat (integralClosure Rhat Pn) := by
    exact
      integralClosure_completedRootTensorComponent_etale_of_ramification_dvd
        (V := V) (C := C) (K := K) (L := L)
        pV hpiV N hN hdiv hCharZero n inferInstance
  let eNormalization : integralClosure Rhat Pn ≃ₐ[Rhat]
      integralClosure Rhat (GenericTensorFieldComponent qF) :=
    genericTensorRefineChosenComponentIntegralClosureAlgEquiv
      (B := Rhat) (K₀ := K) (K₁ := Kroot) (F := Fhat) (L := L) m qF
  exact Algebra.Etale.of_equiv eNormalization

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.FractionRing
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.StandardCompletion

/-!
# The fraction field of the selected-root standard completion

The standard valued-field completion of the selected root DVR and the
fraction field of the completed pure-root ring are canonically equivalent.
This is the fraction-field lift of the valuation-subring equivalence already
constructed in `SelectedRootPrimeStandardCompletion`.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The equivalence between the standard completion of the selected root
DVR's fraction field and the fraction field of the completed pure-root ring.

The equivalence extends the canonical equivalence of their valuation
subrings and fixes the original selected-root fraction field. -/
noncomputable def
    adjoinRootLocalizationAtRootPrimeStandardCompletionFieldAlgEquiv
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularRing R]
    {N : ℕ} (hN : 0 < N) {p : R} (hp : Prime p) :
    let P := Ideal.span ({p} : Set R)
    let D := AdjoinRoot (X ^ N - C p)
    let q := Ideal.span
      ({AdjoinRoot.root (X ^ N - C p)} : Set D)
    let : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp
    let : q.IsPrime := Ideal.isPrime_span_singleton_of_prime
      (prime_adjoinRoot_root_of_prime hN hp)
    let : q.LiesOver P := span_root_liesOver_span_radicand hN hp
    let V := Localization.AtPrime P
    let : IsDiscreteValuationRing V :=
      EtaleFundamentalGroups.isDiscreteValuationRing_localizationAtSpan_of_prime
        R p hp
    let K := FractionRing V
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    let pV := algebraMap R V p
    let hmaxV : IsLocalRing.maximalIdeal V =
        Ideal.span ({pV} : Set V) :=
      localizationAtPrime_maximalIdeal_eq_span_of_eq_span P p rfl
    let pHat := standardDVRCompletionValuationSubringElement V K pV
    let Rhat := AdjoinRoot (X ^ N - C pHat)
    let : IsDomain Rhat :=
      completeDVFRootRing_isDomain H pHat
        (standardDVRCompletionValuationSubringElement_isUniformizer
          V K pV hmaxV) N hN
    let Fhat := FractionRing Rhat
    let W := Localization.AtPrime q
    let : Algebra V W :=
      Localization.AtPrime.algebraOfLiesOver P q
    let : IsDomain W :=
      adjoinRootLocalizationAtRootPrime_isDomain hN hp
    let : IsDiscreteValuationRing W :=
      adjoinRootLocalizationAtRootPrime_isDiscreteValuationRing hN hp
    let L := FractionRing W
    let Hw := standardDVFCompletionCompleteDVF W L
    let What := Hw.valuationSubring
    let Lhat := standardDVFCompletionField W L
    let : Algebra W What :=
      standardDVFCompletionValuationSubringAlgebra W L
    let algWhatLhat : Algebra What Lhat :=
      Algebra.ofSubsemiring Hw.valuation.valuationSubring
    let : SMul What Lhat :=
      algWhatLhat.toSMul
    let : IsFractionRing What Lhat :=
      Hw.toDVF.valuationSubring_isFractionRing
    let : Algebra W Rhat :=
      adjoinRootLocalizationAtRootPrimeCompletionAlgebra hN hp
    let : Module.FaithfullyFlat W Rhat :=
      adjoinRootLocalizationAtRootPrimeCompletion_faithfullyFlat hN hp
    let : FaithfulSMul W Rhat :=
      Module.FaithfullyFlat.faithfulSMul
    let : FaithfulSMul W Fhat := FaithfulSMul.trans W Rhat Fhat
    let algLLhat : Algebra L Lhat := standardDVFCompletionAlgebra W L
    let algWLhat : Algebra W Lhat :=
      standardDVFCompletionBaseAlgebra (V := W) (K := L)
    let : SMul L Lhat := algLLhat.toSMul
    let : SMul W Lhat :=
      algWLhat.toSMul
    let : IsScalarTower W L Lhat :=
      standardDVFCompletion_isScalarTower (V := W) (K := L)
    let algLFhat : Algebra L Fhat := FractionRing.liftAlgebra W Fhat
    let : SMul L Fhat := algLFhat.toSMul
    Lhat ≃ₐ[L] Fhat := by
  intro P D q hP hq hLiesOver V hDvrV K H Vhat algVVhat pV hmaxV pHat Rhat hDomainRhat Fhat W
    algVW hDomainW hDvrW L Hw What Lhat algWWhat algWhatLhat smulWhatLhat hFractionWhat
    algWRhat hFaithfullyFlat hFaithfulWRhat hFaithfulWFhat algLLhat algWLhat smulLLhat
    smulWLhat hTowerWLLhat algLFhat smulLFhat
  have hTowerWWhatLhat : IsScalarTower W What Lhat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := W) (K := L)
  have hTowerWLFhat : IsScalarTower W L Fhat :=
    FractionRing.isScalarTower_liftAlgebra W Fhat
  let eBase : What ≃ₐ[W] Rhat :=
    adjoinRootLocalizationAtRootPrimeStandardCompletionAlgEquiv hN hp
  exact IsFractionRing.fieldEquivOfAlgEquiv L Lhat Fhat eBase

end EtaleFundamentalGroups.Kummer

end

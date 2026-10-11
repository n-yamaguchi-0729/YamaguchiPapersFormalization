/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import SchemeTheory.FiniteEtale.Away.AlgEquivTransport
import SchemeTheory.FiniteEtale.Away.EtaleExtension
import SchemeTheory.FiniteEtale.Henselian.PointedEtale
import EtaleFundamentalGroups.Kummer.Completions.NormalizationPrime.ExactTensorTarget

/-!
# Primitive boundary Away at the exact completed normalization prime

A prime `Q` in a finite DVR normalization selects one literal factor of the
completed tensor product.  The same `Q` also selects the generic tensor
component and, inside its normalization, the prime used by the exact
ramification target.

This file transports a primitive Away statement through that exact route.
After tensor base change, projection to the `Q`-factor is an idempotent
localization.  The chosen factor is then identified with the normalization
of the literal generic tensor component.  That normalization is local, so
the specified maximal prime is its maximal ideal and localization there is
an equivalence.  No component comparison, right-coordinate surjectivity, or
degree equality is assumed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uV uC uK uL

/-- Projection through a product decomposition is an idempotent localization,
so an etale boundary map remains etale on each factor. -/
private theorem boundaryAway_of_product_equiv
    {R B ι : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (E : B ≃ₐ[R] ∀ i, A i) (i : ι) (f : R)
    (hAway : (Localization.awayMap (algebraMap R B) f).Etale) :
    (Localization.awayMap (algebraMap R (A i)) f).Etale := by
  classical
  let product := ∀ j, A j
  let productAlgebra : Algebra B product := E.toRingHom.toAlgebra
  let factorAlgebra : Algebra product (A i) := (Pi.evalRingHom A i).toAlgebra
  let factorMap : B →ₐ[R] A i := (Pi.evalAlgHom R A i).comp E.toAlgHom
  let sourceFactorAlgebra : Algebra B (A i) := factorMap.toAlgebra
  let : IsScalarTower B product (A i) := IsScalarTower.of_algebraMap_eq' rfl
  let EoverB : B ≃ₐ[B] product :=
    AlgEquiv.ofRingEquiv (R := B) (f := E.toRingEquiv) (fun _ ↦ rfl)
  let : Algebra.Etale B product := Algebra.Etale.of_equiv EoverB
  let : IsLocalization.Away (Pi.single i 1 : product) (A i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_
      (RingHom.ker_evalRingHom A i) (Pi.evalRingHom A i).surjective
    simp only [IsIdempotentElem, ← Pi.single_mul_left, Pi.single_eq_same, mul_one]
  let : Algebra.Etale product (A i) :=
    Algebra.Etale.of_isLocalizationAway (Pi.single i 1 : product)
  let : Algebra.Etale B (A i) := Algebra.Etale.comp B product (A i)
  let : IsScalarTower R B (A i) :=
    IsScalarTower.of_algebraMap_eq' factorMap.comp_algebraMap.symm
  exact localization_awayMap_etale_of_etale_extension
    (A := R) (C := B) (D := A i) f hAway

/-- The primitive boundary Away map survives in the normalization of the
completed generic tensor component selected by `Q`, and hence at every
specified maximal prime of that normalization.

The projection from the whole completed tensor product to the `Q`-factor is
constructed as the corresponding idempotent localization.  In particular,
the statement does not identify the whole tensor product with one local
factor. -/
theorem
    completedGenericTensorChosenNormalizationPrime_boundaryAway
    {V : Type uV} {C : Type uC} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra K L] [IsScalarTower V K L]
    (Q : (IsLocalRing.maximalIdeal V).primesOver C)
    (f : V)
    (hAway :
      (Localization.awayMap (algebraMap V C) f).Etale) :
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
    let : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    let : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    let : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let m := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let M := GenericTensorFieldComponent m
    let IC := integralClosure Vhat M
    ∀ (q : Ideal IC) (hqMax : q.IsMaximal),
      let : q.IsPrime := hqMax.isPrime
      let D := Localization.AtPrime q
      let : SMul IC D := OreLocalization.instSMulOfIsScalarTower
      let : Algebra Vhat D := OreLocalization.instAlgebra
    @Algebra.Etale
        (Localization.Away (algebraMap V Vhat f))
        (Localization.Away
          (algebraMap Vhat D (algebraMap V Vhat f)))
        (OreLocalization.instCommRing (R := Vhat))
        (OreLocalization.instCommRing (R := D))
        (Localization.awayMap
          (algebraMap Vhat D) (algebraMap V Vhat f)).toAlgebra := by
  classical
  intro H Vhat Khat algVVhat localVVhat flatVVhat algKKhat algVKhat
    smulKKhat smulVKhat towerVKKhat towerVVhatKhat hmax hres m mMax M IC
  let p := IsLocalRing.maximalIdeal V
  let U := completedFiniteBaseChange (R := V) (R' := Vhat) (C := C)
  let A := fun Q' : p.primesOver C ↦
    completedPrimeValuationSubring (L := L) Q'
  let : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let : ∀ Q', Algebra Vhat (A Q') := fun Q' ↦
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let eProduct : U ≃ₐ[Vhat] ∀ Q', A Q' :=
    completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv
      (V := V) (C := C) (K := K) (L := L)
  have hAwayU :
      (Localization.awayMap
        (algebraMap Vhat U) (algebraMap V Vhat f)).Etale :=
    localization_awayMap_tensorProduct_etale
      (R := V) (X := C) (Y := Vhat) f hAway
  have hAwayFactor :
      (Localization.awayMap
        (algebraMap Vhat (A Q)) (algebraMap V Vhat f)).Etale :=
    boundaryAway_of_product_equiv A eProduct Q (algebraMap V Vhat f) hAwayU
  let eIC : IC ≃ₐ[Vhat] A Q :=
    completedGenericTensorChosenIntegralClosureAlgEquiv
      (V := V) (C := C) (K := K) (L := L) Q
  have hAwayIC :
      (Localization.awayMap
        (algebraMap Vhat IC) (algebraMap V Vhat f)).Etale :=
    localization_awayMap_etale_of_algEquiv
      eIC.symm (algebraMap V Vhat f) hAwayFactor
  let : IsLocalRing IC := eIC.symm.toRingEquiv.isLocalRing
  intro q hqMax hqPrime D smulICD algVhatD
  have hq : q = IsLocalRing.maximalIdeal IC :=
    IsLocalRing.eq_maximalIdeal hqMax
  subst q
  let : IsScalarTower Vhat IC D :=
    OreLocalization.instIsScalarTower
  exact
    localization_awayMap_etale_of_tower_algEquiv
      (A := Vhat) (C := IC) (D₀ := IC) (D₁ := D)
      (localizationAtMaximalIdealAlgEquiv IC)
      (algebraMap V Vhat f) hAwayIC

/-- The exact `Q/m/q` completion package, augmented by the primitive Away
map at that same literal normalization prime.

The tensor kernel, the right embedding, the exact ramification target, and
the local Away statement all use the single `q` selected from `Q`.
Surjectivity of the right coordinate and a field-degree comparison are not
part of the interface. -/
theorem
    exists_completedChosenNormalizationPrime_exactTensorTarget_boundaryAway
    {V : Type uV} {C : Type uC} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra K L] [IsScalarTower V K L]
    (Q : (IsLocalRing.maximalIdeal V).primesOver C)
    (N : ℕ) (hQ : Q.1.ramificationIdx V = N)
    (f : V)
    (hAway :
      (Localization.awayMap (algebraMap V C) f).Etale) :
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
    let : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    let : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    let : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    let : FiniteDimensional K L :=
      finiteDimensional_fractionFields_of_finiteModel_exactCoordinate
        (V := V) (C := C) (K := K) (L := L)
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let m := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let M := GenericTensorFieldComponent m
    let vhatMAlgebra : Algebra Vhat M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := Vhat) m
    let : Algebra Vhat M := vhatMAlgebra
    let : SMul Vhat M := vhatMAlgebra.toSMul
    let : IsScalarTower Vhat Khat M :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let U := completedFiniteBaseChange (R := V) (R' := Vhat) (C := C)
    let P := completedBaseChangeChosenPrime (R := V) (R' := Vhat) Q.1
    let j := completedChosenNormalizationAlgHom
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L)
      (K' := Khat) m
    let : Algebra U (integralClosure Vhat M) := j.toAlgebra
    ∃ q : Ideal (integralClosure Vhat M), ∃ hqMax : q.IsMaximal,
      let : q.IsPrime := hqMax.isPrime
      q.LiesOver P ∧
        q.LiesOver (IsLocalRing.maximalIdeal Vhat) ∧
        RingHom.ker
            (genericTensorChosenLocalizationFractionRingHom
              (B := Vhat) (K := K) (F := Khat) (L := L) m q) = m ∧
        Function.Injective
            (genericTensorChosenLocalizationFractionRingRightHom
              (B := Vhat) (K := K) (F := Khat) (L := L) m q) ∧
        ∃ target : CompleteDVF.{_, 0} M,
          ∃ _ : H.valuation.HasExtension target.valuation,
            Module.Finite Vhat target.valuationSubring ∧
              ramificationIndex H.toDVF target.toDVF = N ∧
              let D := Localization.AtPrime q
              let : SMul (integralClosure Vhat M) D :=
                OreLocalization.instSMulOfIsScalarTower
              let : Algebra Vhat D := OreLocalization.instAlgebra
              @Algebra.Etale
                (Localization.Away (algebraMap V Vhat f))
                (Localization.Away
                  (algebraMap Vhat D (algebraMap V Vhat f)))
                (OreLocalization.instCommRing (R := Vhat))
                (OreLocalization.instCommRing (R := D))
              (Localization.awayMap
                  (algebraMap Vhat D) (algebraMap V Vhat f)).toAlgebra := by
  intro H Vhat Khat algVVhat localVVhat flatVVhat algKKhat algVKhat
    smulKKhat smulVKhat towerVKKhat towerVVhatKhat finiteKL hmax hres
    m mMax M vhatMAlgebra algVhatM smulVhatM towerVhatKhatM U P j algUIC
  have hExactCoordinate :=
    exists_completedChosenNormalizationPrime_exactTensorCoordinate_ramificationTarget
      (V := V) (C := C) (K := K) (L := L) Q N hQ
  obtain ⟨q, hqMax, hqOverP, hqOverVhat, hker, hright,
      target, hExt, hfinite, hram⟩ := hExactCoordinate
  refine ⟨q, hqMax, ?_⟩
  intro hqPrime
  refine ⟨hqOverP, hqOverVhat, hker, hright,
    target, hExt, hfinite, hram, ?_⟩
  intro D smulICD algVhatD
  exact
    completedGenericTensorChosenNormalizationPrime_boundaryAway
      (V := V) (C := C) (K := K) (L := L)
      Q f hAway q hqMax

end EtaleFundamentalGroups.Kummer

end

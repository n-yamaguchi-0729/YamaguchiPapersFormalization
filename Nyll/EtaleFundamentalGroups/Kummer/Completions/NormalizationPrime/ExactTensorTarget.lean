/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Chosen.NormalizationPrime
import Nyll.EtaleFundamentalGroups.GenericTensor.ChosenLocalizationFractionRing
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.RamificationIndexExact

/-!
# The exact completed tensor coordinate at a chosen normalization prime

A normalization prime `Q` over the closed point of a DVR determines all of
the completed data used by the selected-branch argument.  This file keeps
those choices synchronized:

* `m` is the literal maximal ideal of `Khat ⊗[K] L` selected by `Q`;
* `q` is a maximal ideal of the normalization of the `m`-component, lying
  over the literal completed closed point selected by `Q`;
* the canonical tensor map to `Frac((IC Vhat M)_q)` has kernel exactly `m`;
* the complete valued target has ramification index exactly the prescribed
  value of `Q`.

Thus later selected-Away transport can use one `Q/m/q`, rather than compare
independently chosen components or primes.  No component equality,
right-coordinate surjectivity, or degree equality is assumed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uV uC uK uL

/-- Fraction fields of a finite integral model form a finite-dimensional
extension in the compatible scalar tower. -/
theorem finiteDimensional_fractionFields_of_finiteModel_exactCoordinate
    {V : Type uV} {C : Type uC} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V]
    [CommRing C] [IsDomain C] [Algebra V C] [Module.Finite V C]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra K L] [IsScalarTower V K L] :
    FiniteDimensional K L := by
  let eGeneric : (K ⊗[V] C) ≃ₐ[K] L :=
    finiteGenericFiberAlgEquiv
  let : Module.Finite K (K ⊗[V] C) :=
    Module.Finite.base_change V K C
  exact Module.Finite.equiv eGeneric.toLinearEquiv

/-- The completed normalization prime, its exact tensor kernel, and its
exact-ramification complete target are all selected from the same original
prime `Q`.

The right tensor coordinate is recorded only as an embedding.  Surjectivity
would be false in this generality and is deliberately not part of the
interface. -/
theorem
    exists_completedChosenNormalizationPrime_exactTensorCoordinate_ramificationTarget
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
    (N : ℕ) (hQ : Q.1.ramificationIdx V = N) :
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
      letI : q.IsMaximal := hqMax
      letI : q.IsPrime := hqMax.isPrime
      q.LiesOver P ∧
        q.LiesOver (IsLocalRing.maximalIdeal Vhat) ∧
        RingHom.ker
            (genericTensorChosenLocalizationFractionRingHom
              (B := Vhat) (K := K) (F := Khat) (L := L) m q) = m ∧
        Function.Injective
            (genericTensorChosenLocalizationFractionRingRightHom
              (B := Vhat) (K := K) (F := Khat) (L := L) m q) ∧
        ∃ target : CompleteDVF.{_, 0} M,
          ∃ hExt : H.valuation.HasExtension target.valuation,
            letI : H.valuation.HasExtension target.valuation := hExt
            Module.Finite Vhat target.valuationSubring ∧
      ramificationIndex H.toDVF target.toDVF = N := by
  classical
  intro H Vhat Khat algVVhat localVVhat flatVVhat algKKhat algVKhat
    smulKKhat smulVKhat towerVKKhat towerVVhatKhat finiteKL hmax hres
    m mMax M vhatMAlgebra algVhatM smulVhatM towerVhatKhatM U P j algUIC
  let IC := integralClosure Vhat M
  let : IsScalarTower Vhat U IC :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  let : Algebra.IsIntegral Vhat IC :=
    IsIntegralClosure.isIntegral_algebra Vhat M
  let : Algebra.IsIntegral U IC := Algebra.IsIntegral.tower_top Vhat
  have hPGeometry :=
    completedBaseChangeChosenPrime_isMaximal_liesOver
      (R := V) (R' := Vhat) hmax hres Q.1
  let : P.IsMaximal := hPGeometry.1
  have hkerP : RingHom.ker (algebraMap U IC) ≤ P := by
    change RingHom.ker j.toRingHom ≤ P
    rw [completedChosenNormalizationAlgHom_ker
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L)
      (K' := Khat) hmax hres Q.1]
    exact (completedBaseChangeChosenGenericPrime_spec
      (R := V) (R' := Vhat) hmax hres Q.1).1
  have hPrimeExist : ∃ q : Ideal IC, q.IsMaximal ∧ q.under U = P :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (R := U) (S := IC) P hkerP
  let q : Ideal IC := Classical.choose hPrimeExist
  have hqMax : q.IsMaximal := (Classical.choose_spec hPrimeExist).1
  have hqComap : q.under U = P := (Classical.choose_spec hPrimeExist).2
  have hqOverP : q.LiesOver P :=
    (Ideal.liesOver_iff q P).mpr hqComap.symm
  let : q.IsPrime := hqMax.isPrime
  have hqOverVhat : q.LiesOver (IsLocalRing.maximalIdeal Vhat) :=
    @Ideal.LiesOver.trans Vhat _ U _ IC _ _ _ _ _ q P _
      hqOverP hPGeometry.2
  have hker :
      RingHom.ker
          (genericTensorChosenLocalizationFractionRingHom
            (B := Vhat) (K := K) (F := Khat) (L := L) m q) = m :=
    genericTensorChosenLocalizationFractionRingHom_ker
      (B := Vhat) (K := K) (F := Khat) (L := L) m q
  have hright :
      Function.Injective
        (genericTensorChosenLocalizationFractionRingRightHom
          (B := Vhat) (K := K) (F := Khat) (L := L) m q) :=
    genericTensorChosenLocalizationFractionRingRightHom_injective
      (B := Vhat) (K := K) (F := Khat) (L := L) m q
  have hTargetExist :=
    exists_completedChosenGenericComponent_completeDVF_ramificationIndex_eq
      (V := V) (C := C) (K := K) (L := L) Q N hQ
  dsimp only at hTargetExist
  obtain ⟨target, hExt, hfinite, hram⟩ := hTargetExist
  refine ⟨q, hqMax, ?_⟩
  refine ⟨hqOverP, hqOverVhat, hker, hright, target, hExt, ?_⟩
  let : H.valuation.HasExtension target.valuation := hExt
  exact ⟨hfinite, hram⟩

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.IntegralClosureBaseChange
import EtaleFundamentalGroups.Completions.Retained.PrimeChain
import EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.RegularPairNoetherian
import EtaleFundamentalGroups.LocalGeometry.RegularPair.IntegrallyClosed
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.HeightTwo

/-!
# Boundary Away for a retained prefix component after completion

An Away-etale normalization of a finite prefix field component remains
Away-etale after maximal-adic completion, component by component.  The
component is the literal one selected by a retained generic tensor prime.

The finite original normalization, its faithful base action, the normality
of the completed regular pair, and all fraction-field towers are constructed
inside the theorem.  No completed comparison or completed Away hypothesis is
exposed to the caller.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

open RingTheory.Sequence

universe uB uK uM

/-- Transport an original boundary-Away statement to the normalization of
the literal prefix component selected after maximal-adic completion. -/
theorem retainedCompletedPrefix_normalization_boundaryAway
    {B : Type uB} {K : Type uK} {M : Type uM}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Field M] [Algebra B M] [Algebra K M] [IsScalarTower B K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (y z : B) (hreg : IsRegular B [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal B)
    (hdim : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (N : Ideal
      ((AdicCompletion (IsLocalRing.maximalIdeal B) B) ⊗[B]
        (integralClosure B M)))
    [N.IsPrime]
    [N.LiesOver
      (⊥ : Ideal (AdicCompletion (IsLocalRing.maximalIdeal B) B))]
    (hAway :
      (Localization.awayMap
        (algebraMap B (integralClosure B M)) y).Etale) :
    let C := integralClosure B M
    let hCFinite : Module.Finite B C :=
      SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
        (K := K) hdim
    letI : Module.Finite B C := hCFinite
    let hCFraction : IsFractionRing C M :=
      IsIntegralClosure.isFractionRing_of_finite_extension B K M C
    letI : IsFractionRing C M := hCFraction
    let hCFaithful : FaithfulSMul B C :=
      (faithfulSMul_iff_algebraMap_injective B C).mpr fun x w hxw ↦ by
        apply (IsFractionRing.injective B K)
        apply (algebraMap K M).injective
        have hxM := congrArg (fun c : C ↦ (c : M)) hxw
        change algebraMap B M x = algebraMap B M w at hxM
        calc
          algebraMap K M (algebraMap B K x) = algebraMap B M x :=
            (IsScalarTower.algebraMap_apply B K M x).symm
          _ = algebraMap B M w := hxM
          _ = algebraMap K M (algebraMap B K w) :=
            IsScalarTower.algebraMap_apply B K M w
    letI : FaithfulSMul B C := hCFaithful
    let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
    let hgeometry :=
      Kummer.maximalAdicCompletion_regularPair_geometry hreg hgen
    let hBhatDomain : IsDomain Bhat := hgeometry.1
    letI : IsDomain Bhat := hBhatDomain
    let hBhatNoetherian : IsNoetherianRing Bhat :=
      Kummer.maximalAdicCompletion_isNoetherianRing_of_regularPair hreg hgen
    letI : IsNoetherianRing Bhat := hBhatNoetherian
    let yhat := algebraMap B Bhat y
    let zhat := algebraMap B Bhat z
    let hregHat : IsRegular Bhat [yhat, zhat] := by
      simpa only [Bhat, yhat, zhat] using hgeometry.2.1
    let hgenHat : Ideal.ofList [yhat, zhat] =
        IsLocalRing.maximalIdeal Bhat := by
      simpa only [Bhat, yhat, zhat] using hgeometry.2.2.1
    let hBhatNormal : IsIntegrallyClosed Bhat :=
      SpecialLocalPurity.isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
        Bhat yhat zhat hregHat hgenHat
    letI : IsIntegrallyClosed Bhat := hBhatNormal
    let Khat := FractionRing Bhat
    let hBhatFaithfullyFlat : Module.FaithfullyFlat B Bhat :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    letI : Module.FaithfullyFlat B Bhat := hBhatFaithfullyFlat
    letI : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
    letI : Algebra K Khat :=
      (IsFractionRing.lift
        (A := B) (K := K) (L := Khat)
        (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
    letI : IsScalarTower B K Khat :=
      IsScalarTower.of_algebraMap_smul fun b x ↦ by
        rw [Algebra.smul_def, Algebra.smul_def]
        change
          (IsFractionRing.lift
            (A := B) (K := K) (L := Khat)
            (FaithfulSMul.algebraMap_injective B Khat))
              (algebraMap B K b) * x =
            algebraMap B Khat b * x
        rw [IsFractionRing.lift_algebraMap]
    let m := retainedCompletedGenericTensorIdeal
      (R := B) (R' := Bhat) (S := C) (K := K) (L := M)
      (K' := Khat) N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := C) (K := K) (L := M)
      (K' := Khat) N
    let Omega := GenericTensorFieldComponent m
    letI : Algebra Bhat Omega :=
      genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) m
    letI : SMul Bhat Omega :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) m).toSMul
    letI : IsScalarTower Bhat Khat Omega :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    (Localization.awayMap
      (algebraMap Bhat (integralClosure Bhat Omega)) yhat).Etale := by
  classical
  dsimp only
  let C := integralClosure B M
  let : Module.Finite B C :=
    SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := K) hdim
  let : IsFractionRing C M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B K M C
  let : FaithfulSMul B C :=
    (faithfulSMul_iff_algebraMap_injective B C).mpr fun x w hxw ↦ by
      apply (IsFractionRing.injective B K)
      apply (algebraMap K M).injective
      have hxM := congrArg (fun c : C ↦ (c : M)) hxw
      change algebraMap B M x = algebraMap B M w at hxM
      calc
        algebraMap K M (algebraMap B K x) = algebraMap B M x :=
          (IsScalarTower.algebraMap_apply B K M x).symm
        _ = algebraMap B M w := hxM
        _ = algebraMap K M (algebraMap B K w) :=
          IsScalarTower.algebraMap_apply B K M w
  let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
  have hgeometry :=
    Kummer.maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Bhat := hgeometry.1
  let : IsNoetherianRing Bhat :=
    Kummer.maximalAdicCompletion_isNoetherianRing_of_regularPair hreg hgen
  let yhat : Bhat := algebraMap B Bhat y
  let zhat : Bhat := algebraMap B Bhat z
  have hregHat : IsRegular Bhat [yhat, zhat] := by
    simpa only [Bhat, yhat, zhat] using hgeometry.2.1
  have hgenHat : Ideal.ofList [yhat, zhat] =
      IsLocalRing.maximalIdeal Bhat := by
    simpa only [Bhat, yhat, zhat] using hgeometry.2.2.1
  let : IsIntegrallyClosed Bhat :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
      Bhat yhat zhat hregHat hgenHat
  let Khat := FractionRing Bhat
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  let : Algebra K Khat :=
    (IsFractionRing.lift
      (A := B) (K := K) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  let : IsScalarTower B K Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := K) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B K b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  let m := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := C) (K := K) (L := M)
    (K' := Khat) N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := B) (R' := Bhat) (S := C) (K := K) (L := M)
    (K' := Khat) N
  let Omega := GenericTensorFieldComponent m
  let : Algebra Bhat Omega :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) m
  let : SMul Bhat Omega :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) m).toSMul
  let : IsScalarTower Bhat Khat Omega :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hyne : y ≠ 0 :=
    (Kummer.prime_of_mem_regularSystem hreg hgen (by simp)).ne_zero
  simpa only [Omega, yhat] using
    (localization_away_integralClosure_genericTensorFieldComponent_etale_of_awayMap
      (A := B) (C := C) (D := Bhat)
      (F := K) (E := M) (K := Khat)
      y hyne hAway m)

end EtaleFundamentalGroups

end

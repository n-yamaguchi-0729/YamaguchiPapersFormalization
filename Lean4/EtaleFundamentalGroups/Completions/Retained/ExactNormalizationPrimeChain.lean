/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Retained.NormalizationPrimeChain
import EtaleFundamentalGroups.Completions.Retained.RegularBranchPrimeChain
import EtaleFundamentalGroups.Ramification.Tensor.FiniteFlat
import EtaleFundamentalGroups.LocalGeometry.DVR.FlatLocalAscent
import EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.PrimeRootCover
import EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.RegularPairNoetherian
import EtaleFundamentalGroups.Normalization.Primes.MinimalLocalizationDomain
import SchemeTheory.LocalGeometry.HeightOne.NormalLocalizationDVR
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed
import EtaleFundamentalGroups.Purity.SpecialLocal.Support
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# An exact retained branch in one completed normalization component

Let `q ≤ p` be a height-one/closed prime chain in a finite flat domain
over a two-dimensional regular local ring.  If `q` lies over a prime regular
parameter and has a prescribed ramification index, maximal-adic completion
retains that exact index at the same right-contraction prime of the literal
tensor square.

The generic prime below that tensor prime fixes one literal component of the
completed generic fibre.  Integral going-up then carries the retained
height-one/closed chain into the normalization of that same component.  The
normalization prime is deliberately not declared to have the same index:
that final equality additionally needs normality of the localized tensor
factor (equivalently, vertical ramification index one).
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe uR uS uL

/-- The completed finite base change used by a retained branch. -/
abbrev MaximalAdicFiniteBaseChange
    (R : Type uR) (S : Type uS)
    [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] :=
  AdicCompletion (maximalIdeal R) R ⊗[R] S

/-- The left scalar algebra on the completed finite base change. -/
@[reducible] noncomputable def maximalAdicFiniteBaseChangeLeftAlgebra
    (R : Type uR) (S : Type uS)
    [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] :
    Algebra (AdicCompletion (maximalIdeal R) R)
      (MaximalAdicFiniteBaseChange R S) :=
  Algebra.TensorProduct.leftAlgebra

/-- The right scalar algebra on the completed finite base change. -/
@[reducible] noncomputable def maximalAdicFiniteBaseChangeRightAlgebra
    (R : Type uR) (S : Type uS)
    [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] :
    Algebra S (MaximalAdicFiniteBaseChange R S) :=
  Algebra.TensorProduct.rightAlgebra

/-- The left inclusion into the completed finite base change. -/
noncomputable def maximalAdicFiniteBaseChangeIncludeLeft
    (R : Type uR) (S : Type uS)
    [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] :
    AdicCompletion (maximalIdeal R) R →ₐ[AdicCompletion (maximalIdeal R) R]
      MaximalAdicFiniteBaseChange R S :=
  Algebra.TensorProduct.includeLeft

/-- The right inclusion into the completed finite base change. -/
noncomputable def maximalAdicFiniteBaseChangeIncludeRight
    (R : Type uR) (S : Type uS)
    [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] :
    S →ₐ[R] MaximalAdicFiniteBaseChange R S :=
  Algebra.TensorProduct.includeRight

/-- The exact tensor-prime data retained by maximal-adic completion.

Contractions are stored as explicit equalities rather than global
`Ideal.LiesOver` instances.  This keeps the unrelated localization and
fraction-field instance graphs out of the public result type. -/
structure AdicRetainedExactTensorPrimeData
    {R : Type uR} {S : Type uS}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S]
    (y : R) (e : ℕ) (q p : Ideal S) where
  /-- The selected generic-component prime in the completed finite base change. -/
  N : Ideal (MaximalAdicFiniteBaseChange R S)
  /-- The retained branch prime in the same completed finite base change. -/
  Q : Ideal (MaximalAdicFiniteBaseChange R S)
  /-- The selected component prime lies below the retained branch prime. -/
  hNQ : N ≤ Q
  /-- The retained branch prime lies below the extended closed prime. -/
  hQP : Q ≤ p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom
  /-- The selected generic-component ideal is prime. -/
  hNPrime : N.IsPrime
  /-- The selected component contracts to the zero ideal of the completed base. -/
  hNOver :
    N.comap (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom = ⊥
  /-- The retained branch ideal is prime. -/
  hQPrime : Q.IsPrime
  /-- The retained branch contracts on the original finite algebra to the chosen prime `q`. -/
  hQOver :
    Q.comap (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom = q
  /-- The left contraction of the retained branch is generated by the completed parameter `y`. -/
  hQBranch :
    Q.comap (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom =
      Ideal.span
        ({algebraMap R (AdicCompletion (maximalIdeal R) R) y} :
          Set (AdicCompletion (maximalIdeal R) R))
  /-- The retained branch has the prescribed ramification index `e` over the completed base. -/
  hQExact :
    letI : Algebra (AdicCompletion (maximalIdeal R) R)
        (MaximalAdicFiniteBaseChange R S) :=
      maximalAdicFiniteBaseChangeLeftAlgebra R S
    Q.ramificationIdx (AdicCompletion (maximalIdeal R) R) = e
  /-- Localization at the branch is a discrete valuation domain in which the selected component
  ideal vanishes. -/
  hQLocal :
    letI : Q.IsPrime := hQPrime
    ∃ hQDomain : IsDomain (Localization.AtPrime Q),
      letI : IsDomain (Localization.AtPrime Q) := hQDomain
      IsDiscreteValuationRing (Localization.AtPrime Q) ∧
        N.map
          (algebraMap (MaximalAdicFiniteBaseChange R S)
            (Localization.AtPrime Q)) = ⊥
  /-- The extension of the closed prime to the completed finite base change is maximal. -/
  hPMaximal :
    (p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom).IsMaximal
  /-- The extended closed prime contracts to the maximal ideal of the completed local base. -/
  hPOver :
    ∃ hRhatLocal : IsLocalRing (AdicCompletion (maximalIdeal R) R),
      letI : IsLocalRing (AdicCompletion (maximalIdeal R) R) := hRhatLocal
      (p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom).comap
          (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom =
        maximalIdeal (AdicCompletion (maximalIdeal R) R)

namespace AdicRetainedExactTensorPrimeData

/-- A retained tensor-prime pair lifts to a prime chain in the normalization
of its selected completed generic component.

All fraction-field and normalization instances are intentionally scoped to
this predicate instead of being threaded through the enclosing theorem. -/
def HasNormalizationChain
    {R : Type uR} {S : Type uS} {L : Type uL}
    [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    {y : R} {e : ℕ} {q p : Ideal S}
    (z : R) (hreg : IsRegular R [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal R)
    (data : AdicRetainedExactTensorPrimeData y e q p) : Prop :=
  let Rhat := AdicCompletion (maximalIdeal R) R
  let hRhatGeometry :=
    Kummer.maximalAdicCompletion_regularPair_geometry
      (B := R) (x := y) (y := z) hreg hgen
  letI : IsDomain Rhat := hRhatGeometry.1
  let T := MaximalAdicFiniteBaseChange R S
  letI : Algebra Rhat T := maximalAdicFiniteBaseChangeLeftAlgebra R S
  let P := p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom
  letI : data.N.IsPrime := data.hNPrime
  letI : data.N.LiesOver (⊥ : Ideal Rhat) := ⟨by
    change (⊥ : Ideal Rhat) =
      data.N.comap (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom
    exact data.hNOver.symm⟩
  letI : data.Q.IsPrime := data.hQPrime
  letI : P.IsMaximal := data.hPMaximal
  let K := FractionRing R
  let Khat := FractionRing Rhat
  let rLAlgebra : Algebra R L :=
    ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  letI : Algebra R L := rLAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul R L := FaithfulSMul.trans R S L
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let rKhatAlgebra : Algebra R Khat :=
    ((algebraMap Rhat Khat).comp (algebraMap R Rhat)).toAlgebra
  letI : Algebra R Khat := rKhatAlgebra
  letI : Module.FaithfullyFlat R Rhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : @IsScalarTower R Rhat Khat
      (inferInstance : Algebra R Rhat).toSMul
      (inferInstance : Algebra Rhat Khat).toSMul
      rKhatAlgebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : @FaithfulSMul R Khat rKhatAlgebra.toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective
      R Khat _ _ rKhatAlgebra).mpr
    exact (IsFractionRing.injective Rhat Khat).comp
      (FaithfulSMul.algebraMap_injective R Rhat)
  letI : Algebra K Khat := FractionRing.liftAlgebra R Khat
  letI : @IsScalarTower R K Khat
      (inferInstance : Algebra R K).toSMul
      (inferInstance : Algebra K Khat).toSMul
      rKhatAlgebra.toSMul :=
    FractionRing.isScalarTower_liftAlgebra R Khat
  HasRetainedCompletedNormalizationPrimeChain
    (R := R) (R' := Rhat) (S := S) (K := K) (L := L)
    (K' := Khat) data.N data.Q P

end AdicRetainedExactTensorPrimeData

/-- Produce the height-one/DVR data while keeping its auxiliary instances
inside the proof rather than in the result type. -/
private theorem exists_adicCompletion_retainedExactTensorPrimeData
    {R : Type uR} {S : Type uS}
    [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] [FaithfulSMul R S]
    {y z : R} (hy : Prime y)
    (hreg : IsRegular R [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal R)
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    [CharZero (R ⧸ Ideal.span ({y} : Set R))]
    {e : ℕ}
    (q p : Ideal S) [q.IsPrime] [p.IsMaximal]
    [q.LiesOver (Ideal.span ({y} : Set R))]
    [p.LiesOver (maximalIdeal R)]
    (hqp : q ≤ p) (hqExact : q.ramificationIdx R = e) :
    Nonempty (AdicRetainedExactTensorPrimeData y e q p) := by
  classical
  let Rhat := AdicCompletion (maximalIdeal R) R
  have hcompletion :=
    Kummer.maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hcompletion.1
  have hRhatNoetherian : IsNoetherianRing Rhat :=
    Kummer.maximalAdicCompletion_isNoetherianRing_of_regularPair hreg hgen
  have hRhatRegularLocal : IsRegularLocalRing Rhat := by
    let : IsNoetherianRing Rhat := hRhatNoetherian
    exact Kummer.isRegularLocalRing_of_regularSystem
      [algebraMap R Rhat y, algebraMap R Rhat z]
      hcompletion.2.1 hcompletion.2.2.1
  have hRhatLocal : IsLocalRing Rhat := by
    let : IsRegularLocalRing Rhat := hRhatRegularLocal
    infer_instance
  let T := MaximalAdicFiniteBaseChange R S
  let : Algebra Rhat T := maximalAdicFiniteBaseChangeLeftAlgebra R S
  let : Algebra S T := maximalAdicFiniteBaseChangeRightAlgebra R S
  let : IsScalarTower R Rhat T := inferInstance
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let P := p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom
  have hLeftAlgebraMap :
      algebraMap Rhat T =
        (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom := by
    ext x
    rfl
  have hRightAlgebraMap :
      algebraMap S T =
        (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom := by
    ext x
    rfl
  obtain
      ⟨N, Q, hNQ, hQP, hNPrime, hNOver, hQPrime, hQOver,
        hQBranch, hPMax, hPOver⟩ :=
    by
      letI : IsNoetherianRing Rhat := hRhatNoetherian
      letI : IsRegularLocalRing Rhat := hRhatRegularLocal
      exact
        exists_adicCompletion_genericPrime_le_regularBranch_le_retainedClosedPrime
          (R := R) (S := S) hreg hgen q p hqp
            (q.over_def (Ideal.span ({y} : Set R))).symm
  have hQRight :
      Q.comap (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom = q := by
    let : Q.LiesOver q := hQOver
    rw [← hRightAlgebraMap]
    exact (Q.over_def q).symm
  have hQExact : Q.ramificationIdx Rhat = e :=
    by
      let : Q.IsPrime := hQPrime
      let : Q.LiesOver q := hQOver
      let : Q.LiesOver
          (Ideal.span ({algebraMap R Rhat y} : Set Rhat)) := hQBranch
      exact
        ramificationIdx_tensorProduct_span_eq_of_finite_flat_charZero_of_eq
          (R := R) (S := S) (R' := Rhat)
          (y := y) (q := q) (Q := Q)
          (by simpa [maximalAdicFiniteBaseChangeIncludeRight] using hQRight)
          hqExact
  have hyHeight : (Ideal.span ({y} : Set R)).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hy.ne_zero) hy.not_isUnit
  have hqHeight : q.height = 1 := by
    let : IsIntegrallyClosed R :=
      SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
        hdim
    let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
    let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    calc
      q.height = (q.under R).height :=
        SpecialLocalPurity.height_eq_height_under_of_faithfully_integral_over_integrallyClosed q
      _ = (Ideal.span ({y} : Set R)).height :=
        congrArg Ideal.height
          (q.over_def (Ideal.span ({y} : Set R))).symm
      _ = 1 := hyHeight
  let V := Localization.AtPrime q
  have hVDVR : IsDiscreteValuationRing V := by
    let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
    exact
      isDiscreteValuationRing_localizationAtPrime_of_normal_noetherian_height_one
        q hqHeight
  let : IsDiscreteValuationRing V := hVDVR
  have hQLocal :
      letI : Q.IsPrime := hQPrime
      ∃ hQDomain : IsDomain (Localization.AtPrime Q),
        letI : IsDomain (Localization.AtPrime Q) := hQDomain
        IsDiscreteValuationRing (Localization.AtPrime Q) ∧
          N.map (algebraMap T (Localization.AtPrime Q)) = ⊥ := by
    let : Q.IsPrime := hQPrime
    let : N.IsPrime := hNPrime
    let : N.LiesOver (⊥ : Ideal Rhat) := hNOver
    let : Q.LiesOver q := hQOver
    let W := Localization.AtPrime Q
    let : Module.Finite Rhat T := Module.Finite.base_change R Rhat S
    let : IsNoetherianRing T := IsNoetherianRing.of_finite Rhat T
    let : IsNoetherianRing W :=
      IsLocalization.isNoetherianRing Q.primeCompl W inferInstance
    let : Algebra V W := Localization.AtPrime.algebraOfLiesOver q Q
    let : IsScalarTower S V W := inferInstance
    let : Module.Flat S T := by
      let commS : (S ⊗[R] Rhat) ≃ₐ[S] T :=
        Algebra.TensorProduct.commRight R S Rhat
      exact Module.Flat.of_linearEquiv commS.symm.toLinearEquiv
    let : Module.Flat V W := by
      rw [Module.flat_iff_of_isLocalization V q.primeCompl]
      exact Module.Flat.trans S T W
    let : IsLocalHom (algebraMap V W) := by
      rw [RingHom.algebraMap_toAlgebra]
      exact Localization.isLocalHom_localRingHom
        q Q (algebraMap S T) Ideal.LiesOver.over
    have hmaxRight : q.map (algebraMap S W) = maximalIdeal W :=
      tensorProduct_localization_right_maximalIdeal_eq_span_of_finite_flat_charZero
        (R := R) (S := S) (R' := Rhat) y q Q hQRight
    have hmaxLocal :
        (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by
      calc
        (maximalIdeal V).map (algebraMap V W) =
            (q.map (algebraMap S V)).map (algebraMap V W) := by
              rw [Localization.AtPrime.map_eq_maximalIdeal]
        _ = q.map (algebraMap S W) := by
          rw [Ideal.map_map, IsScalarTower.algebraMap_eq S V W]
        _ = maximalIdeal W := hmaxRight
    obtain ⟨hWDomain, hWDVR⟩ :=
      exists_isDomain_isDiscreteValuationRing_of_flat_local_of_map_maximalIdeal_eq
        (V := V) (W := W) hmaxLocal
    let : IsDomain W := hWDomain
    let : IsDiscreteValuationRing W := hWDVR
    let : Algebra.IsIntegral Rhat T := Algebra.IsIntegral.of_finite Rhat T
    have hNMapBot : N.map (algebraMap T W) = ⊥ :=
      prime_liesOver_bot_map_eq_bot_localizationAtPrime_of_isDomain
        (R := Rhat) N Q hNQ
    exact ⟨hWDomain, hWDVR, hNMapBot⟩
  refine ⟨{
    N := N
    Q := Q
    hNQ := hNQ
    hQP := by
      rw [← hRightAlgebraMap]
      exact hQP
    hNPrime := hNPrime
    hNOver := ?_
    hQPrime := hQPrime
    hQOver := hQRight
    hQBranch := ?_
    hQExact := hQExact
    hQLocal := hQLocal
    hPMaximal := by
      rw [← hRightAlgebraMap]
      exact hPMax
    hPOver := ⟨hRhatLocal, ?_⟩
  }⟩
  · change N.comap (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom = ⊥
    rw [← hLeftAlgebraMap]
    exact hNOver.over.symm
  · change Q.comap (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom =
      Ideal.span ({algebraMap R Rhat y} : Set Rhat)
    rw [← hLeftAlgebraMap]
    exact hQBranch.over.symm
  · change
      (p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom).comap
          (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom = maximalIdeal Rhat
    rw [← hLeftAlgebraMap, ← hRightAlgebraMap]
    exact hPOver.over.symm

/-- Supply the normalization chain after the tensor-prime data has been
constructed.  Only this declaration sees the fraction-field instance graph. -/
private theorem adicRetainedExactTensorPrimeData_hasNormalizationChain
    {R : Type uR} {S : Type uS} {L : Type uL}
    [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    {y z : R} {e : ℕ} {q p : Ideal S}
    (hreg : IsRegular R [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal R)
    (data : AdicRetainedExactTensorPrimeData y e q p) :
    AdicRetainedExactTensorPrimeData.HasNormalizationChain
      (L := L) z hreg hgen data := by
  classical
  unfold AdicRetainedExactTensorPrimeData.HasNormalizationChain
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  have hcompletion :=
    Kummer.maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hcompletion.1
  let T := MaximalAdicFiniteBaseChange R S
  let : Algebra Rhat T := maximalAdicFiniteBaseChangeLeftAlgebra R S
  let P := p.map (maximalAdicFiniteBaseChangeIncludeRight R S).toRingHom
  let : data.N.IsPrime := data.hNPrime
  let : data.N.LiesOver (⊥ : Ideal Rhat) := ⟨by
    change (⊥ : Ideal Rhat) =
      data.N.comap (maximalAdicFiniteBaseChangeIncludeLeft R S).toRingHom
    exact data.hNOver.symm⟩
  let : data.Q.IsPrime := data.hQPrime
  let : P.IsMaximal := data.hPMaximal
  let K := FractionRing R
  let Khat := FractionRing Rhat
  let rLAlgebra : Algebra R L :=
    ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  let : Algebra R L := rLAlgebra
  let : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul R L := FaithfulSMul.trans R S L
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let rKhatAlgebra : Algebra R Khat :=
    ((algebraMap Rhat Khat).comp (algebraMap R Rhat)).toAlgebra
  let : Algebra R Khat := rKhatAlgebra
  let : Module.FaithfullyFlat R Rhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : @IsScalarTower R Rhat Khat
      (inferInstance : Algebra R Rhat).toSMul
      (inferInstance : Algebra Rhat Khat).toSMul
      rKhatAlgebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : @FaithfulSMul R Khat rKhatAlgebra.toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective
      R Khat _ _ rKhatAlgebra).mpr
    exact (IsFractionRing.injective Rhat Khat).comp
      (FaithfulSMul.algebraMap_injective R Rhat)
  let : Algebra K Khat := FractionRing.liftAlgebra R Khat
  let : @IsScalarTower R K Khat
      (inferInstance : Algebra R K).toSMul
      (inferInstance : Algebra K Khat).toSMul
      rKhatAlgebra.toSMul :=
    FractionRing.isScalarTower_liftAlgebra R Khat
  simpa [P] using
    (exists_retainedCompletedNormalizationPrimeChain
      (R := R) (R' := Rhat) (S := S) (K := K) (L := L)
      (K' := Khat) data.N data.Q P data.hNQ data.hQP)

/-- Retain an exact regular branch through maximal-adic completion and lift
its prime chain to the normalization of the one generic component selected
by that same chain.

The only ramification equality supplied as input is the original one at
`q`.  The completed tensor-prime equality, the literal generic component,
and both normalization primes are produced internally. -/
theorem exists_adicCompletion_retainedExactTensorPrime_normalizationChain
    {R : Type uR} {S : Type uS} {L : Type uL}
    [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] [FaithfulSMul R S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    {y : R} (hy : Prime y)
    (hyQuot : IsRegularLocalRing (R ⧸ Ideal.span ({y} : Set R)))
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    [CharZero (R ⧸ Ideal.span ({y} : Set R))]
    {e : ℕ}
    (q p : Ideal S) [q.IsPrime] [p.IsMaximal]
    [q.LiesOver (Ideal.span ({y} : Set R))]
    [p.LiesOver (maximalIdeal R)]
    (hqp : q ≤ p) (hqExact : q.ramificationIdx R = e) :
    ∃ z : R,
      ∃ hreg : IsRegular R [y, z],
      ∃ hgen : Ideal.ofList [y, z] = maximalIdeal R,
      ∃ data : AdicRetainedExactTensorPrimeData y e q p,
        AdicRetainedExactTensorPrimeData.HasNormalizationChain
          (L := L) z hreg hgen data := by
  classical
  obtain ⟨z, hreg, hgen⟩ :=
    Kummer.exists_regular_pair_of_prime_regular_quotient_dimension_two
      hy hyQuot hdim
  obtain ⟨data⟩ :=
    exists_adicCompletion_retainedExactTensorPrimeData
      (R := R) (S := S) (y := y) (z := z)
      hy hreg hgen hdim q p hqp hqExact
  exact ⟨z, hreg, hgen, data,
    adicRetainedExactTensorPrimeData_hasNormalizationChain
      hreg hgen data⟩

end EtaleFundamentalGroups

end

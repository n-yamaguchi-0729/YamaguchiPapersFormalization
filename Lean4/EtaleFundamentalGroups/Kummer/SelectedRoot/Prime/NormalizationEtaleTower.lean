/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericTensorComponent
import EtaleFundamentalGroups.GenericTensor.ComponentRestrictBase
import EtaleFundamentalGroups.GenericTensor.FieldComponent.Tower
import EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.NormalizationEtaleDescent

/-!
# Etale normalization in a component after a selected root and a further base change

The selected-root descent theorem produces an etale normalization over the
selected root DVR.  This file keeps the selected generic tensor component and
then applies a further normal base change, selecting an arbitrary component of
the resulting generic tensor product.  In particular, the second component is
not replaced by an abstract comparison field.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uR uC uL uB uK₁ uK'

local instance spanSingletonIsPrimeTower
    {R : Type uR} [CommRing R] [IsDomain R]
    {p : R} [hp : Fact (Prime p)] :
    (Ideal.span ({p} : Set R)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime hp.out

/-- Etaleness at a selected root prime is preserved after passing to a
specified generic tensor component over any further normal base.

The public maximal ideal `m` is formed over an arbitrary intermediate
fraction field `K₁`, so it can be the fixed global component.  Restriction to
the canonical fraction field of the branch DVR, contraction through the root
field, and the second-stage ideal are all constructed internally.  Canonical
component equivalences return the result to the original literal quotient
component `m`. -/
theorem integralClosure_selectedRootPrime_genericTensorTowerComponent_etale_of_ramification_dvd
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
    ∀ {K₁ : Type uK₁} [Field K₁]
      [Algebra K K₁] [Algebra K₁ L] [IsScalarTower K K₁ L]
      {B : Type uB} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
      [Algebra W B]
      {K' : Type uK'} [Field K'] [Algebra B K'] [IsFractionRing B K']
      [Algebra W K'] [IsScalarTower W B K']
      [Algebra Kroot K'] [IsScalarTower W Kroot K']
      [Algebra K₁ K'] [Algebra K K'] [IsScalarTower K K₁ K']
      [IsScalarTower K Kroot K']
      [FiniteDimensional Kroot K'],
      ∀ (m : Ideal (K' ⊗[K₁] L)) (hm : m.IsMaximal),
        let : m.IsMaximal := hm
        let M := GenericTensorFieldComponent m
        let : Algebra B M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := B) m
        Algebra.Etale B (integralClosure B M) := by
  classical
  intro hRegular P D q hP hq hqP V hV K pV Rn W aVW hDomainW hDvrW eLocal
    hFreeRn hFreeW Kroot hFaithVW hFaithVKroot aKKroot
  let : IsScalarTower V K Kroot :=
    FractionRing.isScalarTower_liftAlgebra V Kroot
  intro K₁ hFieldK₁ aKK₁ aK₁L hKK₁L B hRingB hDomainB hNormalB aWB
    K' hFieldK' aBK' hFracBK' aWK' hWBK' aKrootK' hWKrootK'
    aK₁K' aKK' hKK₁K' hKKrootK' hFiniteKrootK' m hm hmInstance M bMAlgebra
  let m₀ := genericTensorRestrictBaseIdeal
    (K₀ := K) (K₁ := K₁) (F := K') (L := L) m
  let : m₀.IsMaximal :=
    genericTensorRestrictBaseIdeal_isMaximal
      (K₀ := K) (K₁ := K₁) (F := K') (L := L) m
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := Kroot) (F' := K') (L := L) m₀
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := Kroot) (F' := K') (L := L) m₀
  let E := GenericTensorFieldComponent n
  let wEAlgebra : Algebra W E :=
    genericTensorFieldComponentLeftScalarAlgebra (R := W) n
  let : SMul W E := wEAlgebra.toSMul
  let : Module W E := wEAlgebra.toModule
  let : IsScalarTower W Kroot E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let T := integralClosure W E
  let : IsFractionRing T E :=
    IsIntegralClosure.isFractionRing_of_finite_extension W Kroot E T
  let : Module.Finite W T :=
    IsIntegralClosure.finite W Kroot E T
  let : Algebra.Etale W T :=
    integralClosure_selectedRootPrime_genericTensorComponent_etale_of_ramification_dvd
      hdim hN hdiv hCharZero n inferInstance
  let m₂ := genericTensorTowerSecondIdeal
    (K := K) (F := Kroot) (F' := K') (L := L) m₀
  let : m₂.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K) (F := Kroot) (F' := K') (L := L) m₀
  let M₂ := GenericTensorFieldComponent m₂
  let : Algebra B M₂ := Ideal.instAlgebraQuotient B m₂
  have hEtale₂ : Algebra.Etale B (integralClosure B M₂) := by
    dsimp only [M₂]
    simpa only using
      integralClosure_genericTensorFieldComponent_etale_of_finiteEtale_baseChange
        (A := W) (B := B) (T := T) (F := Kroot) (E := E) (K := K') m₂
  let M₀ := GenericTensorFieldComponent m₀
  let : Algebra B M₀ := Ideal.instAlgebraQuotient B m₀
  let eTower : M₂ ≃ₐ[K'] M₀ :=
    genericTensorTowerSecondComponentAlgEquiv
      (K := K) (F := Kroot) (F' := K') (L := L) m₀
  let eTowerB : M₂ ≃ₐ[B] M₀ :=
    { toRingEquiv := eTower.toRingEquiv
      commutes' := by
        intro x
        change eTower (algebraMap K' M₂ (algebraMap B K' x)) =
          algebraMap K' M₀ (algebraMap B K' x)
        exact eTower.commutes (algebraMap B K' x) }
  have hEtale₀ : Algebra.Etale B (integralClosure B M₀) :=
    Algebra.Etale.of_equiv eTowerB.mapIntegralClosure
  let eRestrict : M₀ ≃ₐ[K'] M :=
    genericTensorRestrictBaseComponentAlgEquiv
      (K₀ := K) (K₁ := K₁) (F := K') (L := L) m
  let eRestrictB : M₀ ≃ₐ[B] M :=
    { toRingEquiv := eRestrict.toRingEquiv
      commutes' := by
        intro x
        change eRestrict (algebraMap K' M₀ (algebraMap B K' x)) =
          algebraMap K' M (algebraMap B K' x)
        exact eRestrict.commutes (algebraMap B K' x) }
  exact Algebra.Etale.of_equiv eRestrictB.mapIntegralClosure

end EtaleFundamentalGroups.Kummer

end

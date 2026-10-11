/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualFactorPrescribedExponent
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorComponent

/-!
# Complete higher-radical tensor components at a prescribed exponent

The degree factorial used by the original complete-DVF wrapper is only one
possible common exponent.  Here the exponent is an arbitrary positive natural
number, and the only arithmetic input is that the actual ramification index of
the selected complete target divides it.

The first three declarations provide the canonical integral root ring and its
fraction field for that exponent.  The final declarations construct the
finite-etale normalization of a selected generic tensor component from the
actual complete target and the divisibility witness.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- The prescribed positive uniformizer-root ring over a complete DVR is a
domain. -/
theorem completeDVFRootRing_isDomain
    {K : Type uK} [Field K]
    (base : CompleteDVF.{uK, uV} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) :
    IsDomain (AdjoinRoot (X ^ N - C varpi)) := by
  exact isDomain_adjoinRoot_X_pow_sub_C_of_prime
    hN varpi (completeDVFUniformizer_prime base varpi hvarpi)

/-- The canonical `K`-algebra structure on the fraction field of a prescribed
positive uniformizer-root ring. -/
@[reducible]
noncomputable def completeDVFRootFractionFieldAlgebra
    {K : Type uK} [Field K]
    (base : CompleteDVF.{uK, uV} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) :
    Algebra K (FractionRing (AdjoinRoot (X ^ N - C varpi))) := by
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  letI : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  letI : IsDomain Rn :=
    completeDVFRootRing_isDomain base varpi hvarpi N hN
  let F := FractionRing Rn
  let g := algebraMap V F
  have hVRn : Function.Injective (algebraMap V Rn) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [degree_X_pow_sub_C hN varpi]
    exact_mod_cast hN.ne'
  have hg : Function.Injective g := by
    intro x y hxy
    apply hVRn
    apply IsFractionRing.injective Rn F
    change algebraMap V F x = algebraMap V F y at hxy
    rw [IsScalarTower.algebraMap_apply V Rn F,
      IsScalarTower.algebraMap_apply V Rn F] at hxy
    exact hxy
  exact (IsFractionRing.lift hg).toAlgebra

/-- The prescribed-root fraction-field algebra is compatible with the
original fraction field of the valuation ring. -/
theorem completeDVFRootFractionField_isScalarTower
    {K : Type uK} [Field K]
    (base : CompleteDVF.{uK, uV} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) :
    let V := base.valuationSubring
    let Rn := AdjoinRoot (X ^ N - C varpi)
    letI : IsDomain Rn :=
      completeDVFRootRing_isDomain base varpi hvarpi N hN
    let F := FractionRing Rn
    @IsScalarTower V K F
      (inferInstance : SMul V K)
      (completeDVFRootFractionFieldAlgebra
        base varpi hvarpi N hN).toSMul
      (inferInstance : SMul V F) := by
  dsimp only
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let F := FractionRing Rn
  let : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  let : IsDomain Rn :=
    completeDVFRootRing_isDomain base varpi hvarpi N hN
  let : Algebra K F :=
    completeDVFRootFractionFieldAlgebra base varpi hvarpi N hN
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap V F x =
    (IsFractionRing.lift (A := V) (K := K) (L := F) _)
      (algebraMap V K x)
  symm
  apply IsFractionRing.lift_algebraMap

/-- A selected generic tensor component at a prescribed positive root
exponent has finite-etale normalization when its actual complete target has
ramification index dividing that exponent. -/
theorem
    integralClosure_pureRadicalFractionFieldGenericTensorComponent_etale_of_completeTarget
    {K : Type uK} {F : Type uF} {L : Type uL}
    [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L]
    (base : CompleteDVF.{uK, uV} K)
    (target : CompleteDVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N)
    (hdiv : ramificationIndex base.toDVF target.toDVF ∣ N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    letI : Algebra Rn P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra
        (K := K) varpi m
    Algebra.Etale Rn (integralClosure Rn P) := by
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.toDVF.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  have hvarpiPrime : Prime varpi :=
    completeDVFUniformizer_prime base varpi hvarpi
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpiPrime
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
  let gamma : AlgebraicClosure L := j rootP
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  have hrootP : rootP ^ N = algebraMap V P varpi :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  have hgamma : gamma ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) := by
    calc
      gamma ^ N = j (rootP ^ N) := (map_pow j rootP N).symm
      _ = j (algebraMap V P varpi) := by rw [hrootP]
      _ = j (algebraMap K P (varpi : K)) := rfl
      _ = algebraMap K (AlgebraicClosure L) (varpi : K) :=
        (j.restrictScalars K).commutes (varpi : K)
  obtain ⟨pi, unit, hpi, hdecomp, ⟨factor⟩⟩ :=
    exists_higherRadicalActualFactorData_of_completeTarget_of_root
      base target varpi hvarpi N hdiv gamma hgamma
  exact integralClosure_tensorComponent_etale_of_higherRadicalActualFactorData
    base.toDVF target.toDVF hN varpi hvarpiPrime m factor

/-- Canonical fraction-field specialization of
`integralClosure_pureRadicalFractionFieldGenericTensorComponent_etale_of_completeTarget`.
-/
theorem integralClosure_completeDVFRootTensorComponent_etale_of_completeTarget
    {K : Type uK} {L : Type uL} [Field K] [Field L]
    [Algebra K L]
    (base : CompleteDVF.{uK, uV} K)
    (target : CompleteDVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N)
    (hdiv : ramificationIndex base.toDVF target.toDVF ∣ N) :
    let V := base.valuationSubring
    letI : IsFractionRing V K :=
      base.toDVF.valuationSubring_isFractionRing
    letI : IsIntegrallyClosed V :=
      base.toDVF.valuationSubring_isIntegrallyClosed
    let Rn := AdjoinRoot (X ^ N - C varpi)
    letI : IsDomain Rn :=
      completeDVFRootRing_isDomain base varpi hvarpi N hN
    let F := FractionRing Rn
    letI : Algebra K F :=
      completeDVFRootFractionFieldAlgebra base varpi hvarpi N hN
    letI : IsScalarTower V K F :=
      completeDVFRootFractionField_isScalarTower
        base varpi hvarpi N hN
    ∀ (m : Ideal (F ⊗[K] L)) (hm : m.IsMaximal),
      letI : m.IsMaximal := hm
      let P := GenericTensorFieldComponent m
      letI : Algebra Rn P :=
        pureRadicalFractionFieldGenericTensorComponentRootAlgebra
          (K := K) varpi m
      Algebra.Etale Rn (integralClosure Rn P) := by
  dsimp only
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  let : IsIntegrallyClosed V :=
    base.toDVF.valuationSubring_isIntegrallyClosed
  let : IsDomain Rn :=
    completeDVFRootRing_isDomain base varpi hvarpi N hN
  let F := FractionRing Rn
  let : Algebra K F :=
    completeDVFRootFractionFieldAlgebra base varpi hvarpi N hN
  let : IsScalarTower V K F :=
    completeDVFRootFractionField_isScalarTower
      base varpi hvarpi N hN
  intro m hm
  let : m.IsMaximal := hm
  exact
    integralClosure_pureRadicalFractionFieldGenericTensorComponent_etale_of_completeTarget
      base target varpi hvarpi N hN hdiv m

end EtaleFundamentalGroups.Kummer

end

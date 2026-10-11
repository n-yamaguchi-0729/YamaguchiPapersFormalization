/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.ActualCompositum.TensorComponent
import EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.ChosenLocalizationAway

/-!
# Exact-root fixed tensor components contain no new target field

For a fixed component of the exact ramification-index radical tensor
product, finite-etaleness of the component normalization lets the
strict-Henselian exact-root source choose a closed local factor before any
away statement is used.  Reapplying the exact degree sandwich to that chosen
factor shows that the canonical right map from the original target field to
the fixed tensor component is bijective.

This is the field comparison needed to transport a primitive boundary-away
map to the fixed full-root component.  No comparison equivalence or degree
equality is assumed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uL uW uFroot

private theorem finiteDimensional_target_of_finite_valuationSubrings_fixedExact
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional K L := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsFractionRing W L := target.valuationSubring_isFractionRing
  let eGeneric : (K ⊗[V] W) ≃ₐ[K] L := finiteGenericFiberAlgEquiv
  let : Module.Finite K (K ⊗[V] W) :=
    Module.Finite.base_change V K W
  exact Module.Finite.equiv eGeneric.toLinearEquiv

/-- A fixed component of the exact ramification-index root tensor product
has the original target field as its canonical right subfield.  The closed
factor used in the degree sandwich is selected internally from normalization
etaleness; no boundary-away hypothesis is needed. -/
theorem
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactRoot
    {K : Type uK} {Froot : Type uFroot} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    (m : Ideal (Froot ⊗[K] L)) [m.IsMaximal]
    (hEtale :
      let P := GenericTensorFieldComponent m
      letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
      letI : Algebra base.valuationSubring P :=
        pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
          (N := ramificationIndex base target) varpi m
      letI : Algebra
          (AdjoinRoot
            (X ^ ramificationIndex base target - C varpi)) P :=
        pureRadicalFractionFieldGenericTensorComponentRootAlgebra
          (K := K) varpi m
      Algebra.Etale
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi))
        (integralClosure
          (AdjoinRoot
            (X ^ ramificationIndex base target - C varpi)) P)) :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    Function.Bijective
      (algebraMap L (GenericTensorFieldComponent m)) := by
  dsimp only at hEtale ⊢
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let B := AdjoinRoot (X ^ e - C varpi)
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  let : FiniteDimensional K L :=
    finiteDimensional_target_of_finite_valuationSubrings_fixedExact
      base target
  let : FiniteDimensional K Froot :=
    pureRadicalFractionField_finiteDimensional he varpi hvarpiPrime
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let : FiniteDimensional K P := Module.Finite.trans L P
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := e) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := e) varpi m
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := e) varpi m
  let rootAlgebra : Algebra B P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
  let : SMul B P := rootAlgebra.toSMul
  let : Algebra B P := rootAlgebra
  let : IsScalarTower B Froot P :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower V B P := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap V P z =
          algebraMap K P (algebraMap V K z) :=
        IsScalarTower.algebraMap_apply V K P z
      _ = algebraMap Froot P
          (algebraMap K Froot (algebraMap V K z)) :=
        IsScalarTower.algebraMap_apply K Froot P
          (algebraMap V K z)
      _ = algebraMap Froot P
          (algebraMap B Froot (algebraMap V B z)) := by
        congr 1
        exact (IsScalarTower.algebraMap_apply V K Froot z).symm.trans
          (IsScalarTower.algebraMap_apply V B Froot z)
      _ = algebraMap B P (algebraMap V B z) :=
        (IsScalarTower.algebraMap_apply B Froot P
          (algebraMap V B z)).symm
  let : Module.Finite V B :=
    (monic_X_pow_sub_C varpi he.ne').finite_adjoinRoot
  let : Algebra.IsIntegral V B := Algebra.IsIntegral.of_finite V B
  exact
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_normalization_etale
      (K := K) (Omega := L) (Froot := Froot) (P := P)
      base target varpi hvarpi hEtale

/-- The sourced actual-factor data for an exact root supplies the
normalization-etaleness input of the preceding fixed-component comparison.
-/
theorem
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactActualFactor
    {K : Type uK} {Froot : Type uFroot} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    (m : Ideal (Froot ⊗[K] L)) [m.IsMaximal]
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := ramificationIndex base target) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        (ramificationIndex_pos_of_moduleFinite base target)
        varpi (dvfUniformizer_prime base varpi hvarpi) m
      HigherRadicalActualFactorData base target varpi
        (ramificationIndex base target) (j rootP)) :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    Function.Bijective
      (algebraMap L (GenericTensorFieldComponent m)) := by
  let e := ramificationIndex base target
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  apply
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactRoot
      (K := K) (Froot := Froot) (L := L)
      base target varpi hvarpi m
  exact
    integralClosure_tensorComponent_etale_of_higherRadicalActualFactorData
      base target he varpi hvarpiPrime m factor

/-- At the exact exponent, the retained unit-absorption factor itself
produces the actual-factor data and hence the fixed-component field
comparison.  No separately chosen higher factor is exposed. -/
theorem
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactUnitFactor
    {K : Type uK} {Froot : Type uFroot} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (pi : target.valuationSubring)
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    (m : Ideal (Froot ⊗[K] L)) [m.IsMaximal]
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := ramificationIndex base target) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        (ramificationIndex_pos_of_moduleFinite base target)
        varpi (dvfUniformizer_prime base varpi hvarpi) m
      HigherRadicalUnitFactorData base target varpi pi
        (ramificationIndex base target) (j rootP)) :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    Function.Bijective
      (algebraMap L (GenericTensorFieldComponent m)) := by
  let V := base.valuationSubring
  let P := GenericTensorFieldComponent m
  let e := ramificationIndex base target
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := e) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      he varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  have hbetaPow : beta ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow
      base he varpi hvarpiPrime m
  let actual : HigherRadicalActualFactorData
      base target varpi e beta :=
    Classical.choice
      (higherRadicalActualFactorData_of_unitFactorData
        base target varpi hvarpi pi e (dvd_refl e)
          beta hbetaPow factor)
  exact
    pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactActualFactor
      (K := K) (Froot := Froot) (L := L)
      base target varpi hvarpi m actual

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactorComponent
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.ActualCompositum.TensorComponent

/-!
# The literal lower unit factor in a fixed higher tensor component

The unit-absorption factor `Cq` first selects its actual component after the
higher radical base change.  A fixed generic tensor component supplies the
higher root in the same algebraic closure.  This file composes those two
canonical comparisons and retains the distinguished `q`-root coordinate.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- The component selected from the same lower unit factor is canonically
the fixed higher generic tensor component.  The actual higher factor used in
the second comparison is sourced from `factor` itself. -/
noncomputable def
    lowerUnitFactorHigherGenericComponentFixedTensorComponentRingEquiv
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (hdiv : ramificationIndex base target ∣ N)
    (pi : target.valuationSubring)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    (m : Ideal (Froot ⊗[K] L)) [m.IsMaximal]
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpiPrime m
      let beta : AlgebraicClosure L := j rootP
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpiPrime m
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :
    let V := base.valuationSubring
    let P := GenericTensorFieldComponent m
    let : IsDiscreteValuationRing V :=
      base.valuationSubring_isDiscreteValuationRing
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let : Algebra L P := genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
    let beta : AlgebraicClosure L := j rootP
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let Fₑ : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    let : Algebra V Fₑ :=
      ((algebraMap K Fₑ).comp (algebraMap V K)).toAlgebra
    let : IsScalarTower V K Fₑ := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] Fₑ :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    let : Algebra Rₑ Fₑ :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let : Algebra Rₑ K' :=
      ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
    let : IsScalarTower Rₑ Fₑ K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    let I := lowerUnitFactorHigherGenericComponentIdeal
      base target varpi pi N beta he hvarpiPrime halphaPow factor
    ((K' ⊗[Rₑ] Cq) ⧸ I) ≃+* P := by
  intro V P hDVR hFrac algLP rootP j beta e alpha Rₑ Cq Fₑ K'
    algVF towerVKF eRₑ algReF algReCq algReKprime towerReFKprime I
  let : FiniteDimensional K Froot :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpiPrime
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let E : IntermediateField Fₑ (AlgebraicClosure L) :=
    targetCompositumOverLowerRadical (K := K) (L := L) e N beta
  let M : IntermediateField Fₑ (AlgebraicClosure L) := E ⊔ K'
  let lowerEquiv :
      ((K' ⊗[Rₑ] Cq) ⧸
          lowerUnitFactorHigherGenericComponentIdeal
            base target varpi pi N beta he hvarpiPrime halphaPow factor) ≃ₐ[K']
        M :=
    lowerUnitFactorHigherGenericComponentAlgEquiv
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  let basePAlgebra : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : SMul V P := basePAlgebra.toSMul
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  have hrootP : rootP ^ N = algebraMap V P varpi :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  have hbetaPow : beta ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) := by
    calc
      beta ^ N = j (rootP ^ N) := (map_pow j rootP N).symm
      _ = j (algebraMap V P varpi) := by rw [hrootP]
      _ = j (algebraMap K P (varpi : K)) :=
        congrArg j (IsScalarTower.algebraMap_apply V K P varpi).symm
      _ = algebraMap K (AlgebraicClosure L) (varpi : K) :=
        (j.restrictScalars K).commutes (varpi : K)
  let actual : HigherRadicalActualFactorData base target varpi N beta :=
    Classical.choice (higherRadicalActualFactorData_of_unitFactorData
      base target varpi hvarpi pi N hdiv beta hbetaPow factor)
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : Algebra Rn P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
  let : Algebra Rn M :=
    higherRadicalActualFactorDataAlgebra base target varpi beta actual
  let higherEquiv : M ≃ₐ[Rn] P :=
    higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv
      base target hN varpi hvarpiPrime m actual
  exact lowerEquiv.toRingEquiv.trans higherEquiv.toRingEquiv

/-- The composite comparison sends the distinguished lower-factor root to
the same `delta` inside the fixed component's chosen algebraic closure. -/
theorem
    lowerUnitFactorHigherGenericComponentFixedTensorComponentRingEquiv_root
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (hdiv : ramificationIndex base target ∣ N)
    (pi : target.valuationSubring)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    (m : Ideal (Froot ⊗[K] L)) [m.IsMaximal]
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpiPrime m
      let beta : AlgebraicClosure L := j rootP
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpiPrime m
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :
    let V := base.valuationSubring
    let P := GenericTensorFieldComponent m
    let : IsDiscreteValuationRing V :=
      base.valuationSubring_isDiscreteValuationRing
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let : Algebra L P := genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
    let beta : AlgebraicClosure L := j rootP
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let Fₑ : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    let : Algebra V Fₑ :=
      ((algebraMap K Fₑ).comp (algebraMap V K)).toAlgebra
    let : IsScalarTower V K Fₑ := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] Fₑ :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    let : Algebra Rₑ Fₑ :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let : Algebra Rₑ K' :=
      ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
    let : IsScalarTower Rₑ Fₑ K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    let I := lowerUnitFactorHigherGenericComponentIdeal
      base target varpi pi N beta he hvarpiPrime halphaPow factor
    let fixedEquiv : ((K' ⊗[Rₑ] Cq) ⧸ I) ≃+* P :=
      lowerUnitFactorHigherGenericComponentFixedTensorComponentRingEquiv
        base target hN varpi hvarpi hdiv pi m he hvarpiPrime halphaPow factor
    j (fixedEquiv (Ideal.Quotient.mk I
      (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q))) = factor.delta := by
  intro V P hDVR hFrac algLP rootP j beta e alpha Rₑ Cq Fₑ K'
    algVF towerVKF eRₑ algReF algReCq algReKprime towerReFKprime I fixedEquiv
  let : FiniteDimensional K Froot :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpiPrime
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let E : IntermediateField Fₑ (AlgebraicClosure L) :=
    targetCompositumOverLowerRadical (K := K) (L := L) e N beta
  let M : IntermediateField Fₑ (AlgebraicClosure L) := E ⊔ K'
  let lowerEquiv :
      ((K' ⊗[Rₑ] Cq) ⧸
          lowerUnitFactorHigherGenericComponentIdeal
            base target varpi pi N beta he hvarpiPrime halphaPow factor) ≃ₐ[K']
        M :=
    lowerUnitFactorHigherGenericComponentAlgEquiv
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  let basePAlgebra : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : SMul V P := basePAlgebra.toSMul
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  have hrootP : rootP ^ N = algebraMap V P varpi :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  have hbetaPow : beta ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) := by
    calc
      beta ^ N = j (rootP ^ N) := (map_pow j rootP N).symm
      _ = j (algebraMap V P varpi) := by rw [hrootP]
      _ = j (algebraMap K P (varpi : K)) :=
        congrArg j (IsScalarTower.algebraMap_apply V K P varpi).symm
      _ = algebraMap K (AlgebraicClosure L) (varpi : K) :=
        (j.restrictScalars K).commutes (varpi : K)
  let actual : HigherRadicalActualFactorData base target varpi N beta :=
    Classical.choice (higherRadicalActualFactorData_of_unitFactorData
      base target varpi hvarpi pi N hdiv beta hbetaPow factor)
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : Algebra Rn P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
  let : Algebra Rn M :=
    higherRadicalActualFactorDataAlgebra base target varpi beta actual
  change j ((higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv
      base target hN varpi hvarpiPrime m actual)
    (lowerEquiv
      (Ideal.Quotient.mk
        (lowerUnitFactorHigherGenericComponentIdeal
          base target varpi pi N beta he hvarpiPrime halphaPow factor)
        (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q)))) = factor.delta
  change j (higherRadicalActualCompositumFieldTensorComponentAlgEquiv
      e hN varpi hvarpiPrime m
    (lowerEquiv
      (Ideal.Quotient.mk
        (lowerUnitFactorHigherGenericComponentIdeal
          base target varpi pi N beta he hvarpiPrime halphaPow factor)
        (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q)))) = factor.delta
  have hHigher :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding_comp_algEquiv_apply
      e hN varpi hvarpiPrime m
      (lowerEquiv (Ideal.Quotient.mk I (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q)))
  have hLower := lowerUnitFactorHigherGenericComponentAlgEquiv_root_coe
    base target varpi pi N beta he hvarpiPrime halphaPow factor
  have hResult := hHigher.trans hLower
  exact hResult

end EtaleFundamentalGroups.Kummer

end

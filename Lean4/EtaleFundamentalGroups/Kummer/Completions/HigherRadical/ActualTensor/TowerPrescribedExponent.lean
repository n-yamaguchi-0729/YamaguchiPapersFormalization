/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FieldComponent.Tower
import EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensor.ComponentPrescribedExponent
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Fixed tensor components at a prescribed radical exponent

This is the arbitrary-exponent form of the complete higher-radical tensor
tower.  A fixed component after the root extension canonically determines its
pre-root component and the second-stage component.  Supplying the actual
complete valuation on that pre-root component, together with the divisibility
of its ramification index by `N`, is enough to prove that the normalization of
the original fixed component is finite etale over the `N`-th root ring.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK₀ uK uV uF uL uW

/-- A fixed component in the two-stage tensor tower has finite-etale
normalization at a prescribed exponent, provided the actual ramification
index of its canonically selected pre-root component divides that exponent.
-/
theorem
    integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_completeTarget
    {K₀ : Type uK₀} {K : Type uK} {F : Type uF} {L : Type uL}
    [Field K₀] [Field K] [Field F] [Field L]
    [Algebra K₀ K] [Algebra K₀ L]
    [Algebra K F]
    [FiniteDimensional K F]
    (base : CompleteDVF.{uK, uV} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    [Algebra K₀ F] [IsScalarTower K₀ K F]
    (m : Ideal (F ⊗[K₀] L)) (hm : m.IsMaximal) :
    letI : m.IsMaximal := hm
    let n := genericTensorTowerIntermediateIdeal
      (K := K₀) (F := K) (F' := F) (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K₀) (F := K) (F' := F) (L := L) m
    let L₀ := GenericTensorFieldComponent n
    ∀ (target : CompleteDVF.{max uK uL, uW} L₀),
      [base.valuation.HasExtension target.valuation] →
      [Module.Finite base.valuationSubring target.valuationSubring] →
      ramificationIndex base.toDVF target.toDVF ∣ N →
      let Rn := AdjoinRoot (X ^ N - C varpi)
      let P := GenericTensorFieldComponent m
      letI : Algebra Rn P :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
      Algebra.Etale Rn (integralClosure Rn P) := by
  dsimp only
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : m.IsMaximal := hm
  let n := genericTensorTowerIntermediateIdeal
    (K := K₀) (F := K) (F' := F) (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K₀) (F := K) (F' := F) (L := L) m
  let L₀ := GenericTensorFieldComponent n
  intro target hExt hfinite hdiv
  let : base.valuation.HasExtension target.valuation := hExt
  let : Module.Finite V target.valuationSubring := hfinite
  let m₂ := genericTensorTowerSecondIdeal
    (K := K₀) (F := K) (F' := F) (L := L) m
  let : m₂.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K₀) (F := K) (F' := F) (L := L) m
  let P₂ := GenericTensorFieldComponent m₂
  let P := GenericTensorFieldComponent m
  let : Algebra Rn P₂ :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m₂
  have hEtale₂ : Algebra.Etale Rn (integralClosure Rn P₂) :=
    integralClosure_pureRadicalFractionFieldGenericTensorComponent_etale_of_completeTarget
      base target varpi hvarpi N hN hdiv m₂
  let : Algebra Rn P :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
  let eF : P₂ ≃ₐ[F] P :=
    genericTensorTowerSecondComponentAlgEquiv
      (K := K₀) (F := K) (F' := F) (L := L) m
  let e : P₂ ≃ₐ[Rn] P :=
    { toRingEquiv := eF.toRingEquiv
      commutes' := by
        intro x
        change eF (algebraMap F P₂ (algebraMap Rn F x)) =
          algebraMap F P (algebraMap Rn F x)
        exact eF.commutes (algebraMap Rn F x) }
  let eIC : integralClosure Rn P₂ ≃ₐ[Rn] integralClosure Rn P :=
    e.mapIntegralClosure
  let : Algebra.Etale Rn (integralClosure Rn P₂) := hEtale₂
  exact Algebra.Etale.of_equiv eIC

/-- Canonical root-fraction-field specialization of
`integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_completeTarget`.
-/
theorem integralClosure_completeDVFRoot_fixedTensorComponent_etale_of_completeTarget
    {K₀ : Type uK₀} {K : Type uK} {L : Type uL}
    [Field K₀] [Field K] [Field L]
    [Algebra K₀ K] [Algebra K₀ L]
    (base : CompleteDVF.{uK, uV} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N) :
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
    letI : Algebra K₀ F :=
      ((algebraMap K F).comp (algebraMap K₀ K)).toAlgebra
    letI : IsScalarTower K₀ K F :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : FiniteDimensional K F :=
      pureRadicalFractionField_finiteDimensional
        hN varpi (completeDVFUniformizer_prime base varpi hvarpi)
    ∀ (m : Ideal (F ⊗[K₀] L)) (hm : m.IsMaximal),
      letI : m.IsMaximal := hm
      let n := genericTensorTowerIntermediateIdeal
        (K := K₀) (F := K) (F' := F) (L := L) m
      letI : n.IsMaximal :=
        genericTensorTowerIntermediateIdeal_isMaximal
          (K := K₀) (F := K) (F' := F) (L := L) m
      let L₀ := GenericTensorFieldComponent n
      ∀ (target : CompleteDVF.{max uK uL, uW} L₀),
        [base.valuation.HasExtension target.valuation] →
        [Module.Finite V target.valuationSubring] →
        ramificationIndex base.toDVF target.toDVF ∣ N →
        let P := GenericTensorFieldComponent m
        letI : Algebra Rn P :=
          genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
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
  let : Algebra K₀ F :=
    ((algebraMap K F).comp (algebraMap K₀ K)).toAlgebra
  let : IsScalarTower K₀ K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional
      hN varpi (completeDVFUniformizer_prime base varpi hvarpi)
  intro m hm target hExt hfinite hdiv
  exact
    integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_completeTarget
      base varpi hvarpi N hN m hm target hdiv

end EtaleFundamentalGroups.Kummer

end

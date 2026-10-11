/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Degree
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Tower
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorComponent
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Complete higher-radical factors in a fixed tensor component

An arbitrary component of `F' ⊗[K₀] L` first selects a component of
`K ⊗[K₀] L`, where `K` is the complete base field, and then a component
after adjoining the factorial root.  The two-stage quotient is canonically
the original component.  This file applies the complete-DVF actual-factor
theorem to that exact second-stage component and transports the resulting
finite-etale normalization back to the originally selected component.

Thus the degree bound is imposed only on the pre-root extension `L / K₀`.
No abstract field-component comparison or post-root degree hypothesis is an
input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField

universe uK₀ uK uV uL

/-- Every fixed component after a complete factorial radical base change has
finite-etale normalization over the integral radical ring.

The contraction to the pre-root tensor product, its maximality, the
second-stage maximal ideal, and the equivalence back to the original fixed
component are all produced canonically. -/
theorem integralClosure_completeDVFFactorialRoot_fixedTensorComponent_etale
    {K₀ : Type uK₀} {K : Type uK} {L : Type uL}
    [Field K₀] [Field K] [Field L]
    [Algebra K₀ K] [Algebra K₀ L]
    [FiniteDimensional K₀ L] [Algebra.IsSeparable K₀ L]
    (base : CompleteDVF.{uK, uV} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) (hdegree : Module.finrank K₀ L ≤ D) :
    let V := base.valuationSubring
    letI : IsFractionRing V K :=
      base.toDVF.valuationSubring_isFractionRing
    letI : IsIntegrallyClosed V :=
      base.toDVF.valuationSubring_isIntegrallyClosed
    let N := D.factorial
    let Rn := AdjoinRoot (X ^ N - C varpi)
    letI : IsDomain Rn :=
      completeDVFFactorialRootRing_isDomain base varpi hvarpi D
    let F := FractionRing Rn
    letI : Algebra K F :=
      completeDVFFactorialRootFractionFieldAlgebra base varpi hvarpi D
    letI : IsScalarTower V K F :=
      completeDVFFactorialRootFractionField_isScalarTower
        base varpi hvarpi D
    letI : Algebra K₀ F :=
      ((algebraMap K F).comp (algebraMap K₀ K)).toAlgebra
    letI : IsScalarTower K₀ K F :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∀ (m : Ideal (F ⊗[K₀] L)) (hm : m.IsMaximal),
      letI : m.IsMaximal := hm
      let P := GenericTensorFieldComponent m
      letI : Algebra Rn P :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
      Algebra.Etale Rn (integralClosure Rn P) := by
  dsimp only
  let V := base.valuationSubring
  let N := D.factorial
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  let : IsIntegrallyClosed V :=
    base.toDVF.valuationSubring_isIntegrallyClosed
  let : IsDomain Rn :=
    completeDVFFactorialRootRing_isDomain base varpi hvarpi D
  let F := FractionRing Rn
  let : Algebra K F :=
    completeDVFFactorialRootFractionFieldAlgebra base varpi hvarpi D
  let : IsScalarTower V K F :=
    completeDVFFactorialRootFractionField_isScalarTower
      base varpi hvarpi D
  let : Algebra K₀ F :=
    ((algebraMap K F).comp (algebraMap K₀ K)).toAlgebra
  let : IsScalarTower K₀ K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional
      (Nat.factorial_pos D) varpi
        (completeDVFUniformizer_prime base varpi hvarpi)
  intro m hm
  let : m.IsMaximal := hm
  let n := genericTensorTowerIntermediateIdeal
    (K := K₀) (F := K) (F' := F) (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K₀) (F := K) (F' := F) (L := L) m
  let L₀ := GenericTensorFieldComponent n
  let m₂ := genericTensorTowerSecondIdeal
    (K := K₀) (F := K) (F' := F) (L := L) m
  let : m₂.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K₀) (F := K) (F' := F) (L := L) m
  let P₂ := GenericTensorFieldComponent m₂
  let P := GenericTensorFieldComponent m
  have hdegree₀ : Module.finrank K L₀ ≤ D :=
    (genericTensorFieldComponent_finrank_le n).trans hdegree
  let : Algebra Rn P₂ :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m₂
  have hEtale₂ : Algebra.Etale Rn (integralClosure Rn P₂) :=
    integralClosure_completeDVFFactorialRootTensorComponent_etale
      base varpi hvarpi D hdegree₀ m₂ inferInstance
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

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.ActualCompositum.TensorComponent

/-!
# Canonical complete-DVF higher-radical tensor components

For a complete discrete valuation field `K`, this file equips the fraction
field of the factorial uniformizer-root ring with its canonical `K`-algebra
structure.  The construction is the localization lift of the inclusion of
the valuation ring.  It therefore supplies, rather than assumes, the scalar
tower needed by the fixed generic tensor component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField

universe u v w

/-- A uniformizer of a complete discrete valuation field is prime in its
valuation ring. -/
theorem completeDVFUniformizer_prime
    {K : Type u} [Field K]
    (base : CompleteDVF.{u, v} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K)) :
    Prime varpi := by
  let V := base.valuationSubring
  have hmaxV : IsLocalRing.maximalIdeal V = Ideal.span {varpi} := by
    change IsLocalRing.maximalIdeal base.valuation.valuationSubring =
      Ideal.span {varpi}
    exact Valuation.IsUniformizer.is_generator hvarpi
  have hvarpi_ne : varpi ≠ 0 := by
    intro hzero
    apply hvarpi.ne_zero
    exact congrArg Subtype.val hzero
  apply (Ideal.span_singleton_prime hvarpi_ne).mp
  exact Eq.mp (congrArg Ideal.IsPrime hmaxV)
    (IsLocalRing.maximalIdeal.isMaximal V).isPrime

/-- The factorial uniformizer-root ring over a complete DVR is a domain.

The positivity of the exponent and primality of the radicand are both
constructed from the displayed primitive data. -/
theorem completeDVFFactorialRootRing_isDomain
    {K : Type u} [Field K]
    (base : CompleteDVF.{u, v} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) :
    IsDomain (AdjoinRoot (X ^ D.factorial - C varpi)) := by
  exact isDomain_adjoinRoot_X_pow_sub_C_of_prime
    (Nat.factorial_pos D) varpi
    (completeDVFUniformizer_prime base varpi hvarpi)

/-- The canonical `K`-algebra structure on the fraction field of the
factorial uniformizer-root ring.

It is obtained by lifting the injective map from the valuation ring through
its fraction field `K`. -/
@[reducible]
noncomputable def completeDVFFactorialRootFractionFieldAlgebra
    {K : Type u} [Field K]
    (base : CompleteDVF.{u, v} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) :
    Algebra K
      (FractionRing (AdjoinRoot (X ^ D.factorial - C varpi))) := by
  let V := base.valuationSubring
  let N := D.factorial
  let Rn := AdjoinRoot (X ^ N - C varpi)
  letI : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  letI : IsDomain Rn :=
    completeDVFFactorialRootRing_isDomain base varpi hvarpi D
  let F := FractionRing Rn
  let g := algebraMap V F
  have hVRn : Function.Injective (algebraMap V Rn) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [degree_X_pow_sub_C (Nat.factorial_pos D) varpi]
    exact_mod_cast (Nat.factorial_pos D).ne'
  have hg : Function.Injective g := by
    intro x y hxy
    apply hVRn
    apply IsFractionRing.injective Rn F
    change algebraMap V F x = algebraMap V F y at hxy
    rw [IsScalarTower.algebraMap_apply V Rn F,
      IsScalarTower.algebraMap_apply V Rn F] at hxy
    exact hxy
  exact (IsFractionRing.lift hg).toAlgebra

/-- The localization lift defining the canonical radical fraction field is
compatible with the original valuation-ring fraction field. -/
theorem completeDVFFactorialRootFractionField_isScalarTower
    {K : Type u} [Field K]
    (base : CompleteDVF.{u, v} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) :
    let V := base.valuationSubring
    let N := D.factorial
    let Rn := AdjoinRoot (X ^ N - C varpi)
    letI : IsDomain Rn :=
      completeDVFFactorialRootRing_isDomain base varpi hvarpi D
    let F := FractionRing Rn
    @IsScalarTower V K F
      (inferInstance : SMul V K)
      (completeDVFFactorialRootFractionFieldAlgebra
        base varpi hvarpi D).toSMul
      (inferInstance : SMul V F) := by
  dsimp only
  let V := base.valuationSubring
  let N := D.factorial
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let F := FractionRing Rn
  let : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  let : IsDomain Rn :=
    completeDVFFactorialRootRing_isDomain base varpi hvarpi D
  let : Algebra K F :=
    completeDVFFactorialRootFractionFieldAlgebra base varpi hvarpi D
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap V F x =
    (IsFractionRing.lift (A := V) (K := K) (L := F) _)
      (algebraMap V K x)
  symm
  apply IsFractionRing.lift_algebraMap

/-- The normalization of every fixed maximal generic component of the
canonical factorial uniformizer-root fraction field is finite étale over
the integral root ring.

All auxiliary data are produced internally: the `K`-structure on the
fraction field, the selected root in the tensor component, its embedding in
`AlgebraicClosure L`, the complete target valuation, the actual compositum
factor, and the root-compatible integral-closure comparison. -/
theorem
    integralClosure_completeDVFFactorialRootTensorComponent_etale
    {K : Type u} {L : Type w} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : CompleteDVF.{u, v} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) (hdegree : Module.finrank K L ≤ D) :
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
    ∀ (m : Ideal (F ⊗[K] L)) (hm : m.IsMaximal),
      letI : m.IsMaximal := hm
      let P := GenericTensorFieldComponent m
      letI : Algebra Rn P :=
        pureRadicalFractionFieldGenericTensorComponentRootAlgebra
          (K := K) varpi m
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
  intro m hm
  let : m.IsMaximal := hm
  exact
    integralClosure_pureRadicalFractionFieldGenericTensorComponent_etale_of_completeBase
      (F := F) base varpi hvarpi D hdegree m

end EtaleFundamentalGroups.Kummer

end

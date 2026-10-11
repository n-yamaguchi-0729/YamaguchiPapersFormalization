/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorComponent
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Complete-DVF higher-radical tensor products

The actual-factor theorem applies to each literal maximal component of the
generic tensor product.  Finite separability decomposes that tensor product
into exactly those components, so their integral closures assemble into an
etale normalization of the original tensor product.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField

universe u v w

/-- Over a complete discrete valuation field, the normalization of the
factorial uniformizer-root generic tensor product is etale over the integral
root ring.  All selected actual factors are constructed componentwise and
then assembled through the canonical Artinian product decomposition. -/
theorem integralClosure_completeDVFFactorialRootTensorProduct_etale
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
    let G := F ⊗[K] L
    letI : Algebra Rn G :=
      genericTensorProductLeftScalarAlgebra
        (R := Rn) (K := K) (F := F) (L := L)
    Algebra.Etale Rn (integralClosure Rn G) := by
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
  let G := F ⊗[K] L
  let : Algebra Rn G :=
    genericTensorProductLeftScalarAlgebra
      (R := Rn) (K := K) (F := F) (L := L)
  apply integralClosure_genericTensorProduct_etale
  intro m hm
  let : m.IsMaximal := hm
  exact
    integralClosure_completeDVFFactorialRootTensorComponent_etale
      base varpi hvarpi D hdegree m hm

end EtaleFundamentalGroups.Kummer

end

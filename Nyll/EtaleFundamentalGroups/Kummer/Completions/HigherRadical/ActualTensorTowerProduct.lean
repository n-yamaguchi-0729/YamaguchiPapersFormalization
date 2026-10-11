/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorTower

/-!
# Complete higher-radical tensor products over an earlier base field

Let `K₀ → K` be a complete-field base change and let `F` be the fraction
field of the factorial uniformizer-root ring over the valuation ring of `K`.
Every component of `F ⊗[K₀] L` has finite-etale normalization by the
fixed-component tower theorem.  The canonical product decomposition of this
finite separable tensor product then gives the same conclusion for the
normalization in the original tensor product itself.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField

universe uK₀ uK uV uL

/-- The normalization of the original post-root tensor product is etale over
the integral factorial root ring.

The intermediate and second-stage components used in the proof are all
selected from each literal maximal ideal of this same tensor product.  No
comparison of abstract component fields is an input. -/
theorem integralClosure_completeDVFFactorialRoot_originalTensorProduct_etale
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
    let G := F ⊗[K₀] L
    letI : Algebra Rn G :=
      genericTensorProductLeftScalarAlgebra
        (R := Rn) (K := K₀) (F := F) (L := L)
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
  let : Algebra K₀ F :=
    ((algebraMap K F).comp (algebraMap K₀ K)).toAlgebra
  let : IsScalarTower K₀ K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let G := F ⊗[K₀] L
  let : Algebra Rn G :=
    genericTensorProductLeftScalarAlgebra
      (R := Rn) (K := K₀) (F := F) (L := L)
  apply integralClosure_genericTensorProduct_etale
  intro m hm
  let : m.IsMaximal := hm
  exact
    integralClosure_completeDVFFactorialRoot_fixedTensorComponent_etale
      base varpi hvarpi D hdegree m hm

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Finite
import EtaleFundamentalGroups.Kummer.HigherRadical.FixedTensor.IntrinsicCoordinates

/-!
# The literal finite-etale factor over a prescribed higher radical

`HigherRadicalUnitFactorData` retains the exact integral unit factor `Cq`
selected at the actual ramification index.  This file supplies its module
finiteness over that lower radical and then base-changes the same factor to
an arbitrary prescribed higher root.  The final coordinate identity records
that no new factor is selected by this base change.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

/-- The exact lower unit factor retained in `HigherRadicalUnitFactorData` is
module-finite over the actual ramification-index radical. -/
theorem higherRadicalUnitFactorData_radical_finite
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    Module.Finite Rₑ Cq := by
  dsimp only
  let V := base.valuationSubring
  let W := target.valuationSubring
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Cq := AdjoinRoot factor.q
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let : IsScalarTower V Rₑ Cq :=
    IsScalarTower.of_algebraMap_eq fun z ↦
      (factor.radicalToUnitFactor.commutes z).symm
  let : Module.Finite V Rₑ :=
    (monic_X_pow_sub_C varpi
      (ramificationIndex_pos_of_moduleFinite base target).ne').finite_adjoinRoot
  let : Module.Finite W Cq := factor.q_finite
  let : Module.Finite V Cq := Module.Finite.trans W Cq
  exact Module.Finite.of_restrictScalars_finite V Rₑ Cq

/-- Base change of the same actual unit factor to any prescribed higher
uniformizer root is finite etale. -/
theorem higherRadicalUnitFactorData_higher_finiteEtale
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (hdiv : ramificationIndex base target ∣ N)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    letI : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    Algebra.Etale Rₙ (Rₙ ⊗[Rₑ] Cq) ∧
      Module.Finite Rₙ (Rₙ ⊗[Rₑ] Cq) := by
  dsimp only
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
    adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let : Algebra.Etale Rₑ Cq := factor.radical_etale
  let : Module.Finite Rₑ Cq :=
    higherRadicalUnitFactorData_radical_finite
      base target varpi pi N beta factor
  exact ⟨inferInstance, Module.Finite.base_change Rₑ Rₙ Cq⟩

/-- In the higher base change, the prescribed higher root to the quotient
power is the distinguished lower-factor root times the target uniformizer.
This is the literal coordinate identity inherited from `factor`; it does
not pass through an abstractly reselected component. -/
theorem higherRadicalUnitFactorData_higher_root_coordinate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (hdiv : ramificationIndex base target ∣ N)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    letI : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    (AdjoinRoot.root (X ^ N - C varpi) ^ (N / e)) ⊗ₜ[Rₑ] (1 : Cq) =
      (1 : Rₙ) ⊗ₜ[Rₑ]
        (AdjoinRoot.root factor.q *
          algebraMap target.valuationSubring Cq pi) := by
  dsimp only
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
    adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  rw [← adjoinRootPowerMapOfDvd_root hdiv varpi]
  change algebraMap Rₑ Rₙ
      (AdjoinRoot.root (X ^ e - C varpi)) ⊗ₜ[Rₑ] (1 : Cq) = _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  change (1 : Rₙ) ⊗ₜ[Rₑ]
      factor.radicalToUnitFactor
        (AdjoinRoot.root (X ^ e - C varpi)) = _
  rw [factor.radical_root]

end EtaleFundamentalGroups.Kummer

end

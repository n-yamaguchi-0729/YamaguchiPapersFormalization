/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.FieldOverLowerFractionRing
import EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor

/-!
# The higher radical field inside an actual factor

The canonical higher radical field is a subfield of the actual compositum.
For an arbitrary `HigherRadicalActualFactorData`, its root-ring action agrees
with the composite through that subfield.  This supplies the scalar tower
needed to retain the whole higher-root action through later components.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped TensorProduct

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uL uW

/-- The canonical action of the embedded higher radical field on the actual
compositum, induced by inclusion of intermediate fields. -/
@[reducible]
noncomputable def higherRadicalActualFactorHigherFieldAlgebra
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (beta : AlgebraicClosure L) :
    let e := ramificationIndex base target
    let K' := higherRadicalFieldOverLower (K := K) e N beta
    let M := higherRadicalActualCompositumField
      (K := K) (L := L) e N beta
    Algebra K' M := by
  dsimp only
  exact (IntermediateField.inclusion
    (show higherRadicalFieldOverLower (K := K)
        (ramificationIndex base target) N beta ≤
      higherRadicalActualCompositumField
        (K := K) (L := L) (ramificationIndex base target) N beta
      from le_sup_right)).toRingHom.toAlgebra

/-- The root-ring map of an actual higher-radical factor is the composite
through the canonical embedded higher radical field. -/
theorem higherRadicalActualFactor_algebraMap_comp_eq_rootMap
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring) (hvarpiPrime : Prime varpi)
    (beta : AlgebraicClosure L)
    (hbetaPow :
      beta ^ N = algebraMap K (AlgebraicClosure L) (varpi : K))
    (actual : HigherRadicalActualFactorData
      base target varpi N beta) :
    let e := ramificationIndex base target
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let F := lowerRadicalField (K := K) e N beta
    let K' := higherRadicalFieldOverLower (K := K) e N beta
    let M := higherRadicalActualCompositumField
      (K := K) (L := L) e N beta
    letI : Algebra K K' :=
      ((algebraMap F K').comp (algebraMap K F)).toAlgebra
    letI : Algebra Rₙ K' :=
      higherRadicalFieldOverLowerRootAlgebra
        (e := e) base hN varpi hvarpiPrime beta hbetaPow
    letI : Algebra K' M :=
      higherRadicalActualFactorHigherFieldAlgebra base target beta
    (algebraMap K' M).comp (algebraMap Rₙ K') = actual.rootMap := by
  dsimp only
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let F := lowerRadicalField (K := K) e N beta
  let K' := higherRadicalFieldOverLower (K := K) e N beta
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N beta
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra K K' :=
    ((algebraMap F K').comp (algebraMap K F)).toAlgebra
  let eRₙ : (K ⊗[V] Rₙ) ≃ₐ[K] K' :=
    higherRadicalFieldOverLowerGenericFiberAlgEquiv
      (e := e) base hN varpi hvarpiPrime beta hbetaPow
  let : Algebra Rₙ K' :=
    higherRadicalFieldOverLowerRootAlgebra
      (e := e) base hN varpi hvarpiPrime beta hbetaPow
  let : Algebra K' M :=
    higherRadicalActualFactorHigherFieldAlgebra base target beta
  have hRₙRoot :
      (((genericFiberRightAlgHom eRₙ)
          (AdjoinRoot.root (X ^ N - C varpi)) : K') :
        AlgebraicClosure L) = beta := by
    change (((pureRadicalGenericFiberAlgEquiv hN varpi hvarpiPrime beta
        hbetaPow) (1 ⊗ₜ[V] AdjoinRoot.root (X ^ N - C varpi)) :
      IntermediateField.adjoin K ({beta} : Set (AlgebraicClosure L))) :
        AlgebraicClosure L) = beta
    exact congrArg Subtype.val
      (pureRadicalGenericFiberAlgEquiv_tmul_root
        hN varpi hvarpiPrime beta hbetaPow)
  have hRₙBase (z : V) :
      (((genericFiberRightAlgHom eRₙ)
          (algebraMap V Rₙ z) : K') : AlgebraicClosure L) =
        algebraMap K (AlgebraicClosure L) (z : K) := by
    rw [(genericFiberRightAlgHom eRₙ).commutes]
    rfl
  apply AdjoinRoot.ringHom_ext
  · ext z
    exact hRₙBase z |>.trans (actual.commutes_coe z).symm
  · apply Subtype.ext
    exact hRₙRoot.trans actual.root_coe.symm

/-- The canonical higher radical field, the actual compositum, and the
literal higher root ring form a scalar tower. -/
theorem higherRadicalActualFactor_isScalarTower
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring) (hvarpiPrime : Prime varpi)
    (beta : AlgebraicClosure L)
    (hbetaPow :
      beta ^ N = algebraMap K (AlgebraicClosure L) (varpi : K))
    (actual : HigherRadicalActualFactorData
      base target varpi N beta) :
    let e := ramificationIndex base target
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let F := lowerRadicalField (K := K) e N beta
    let K' := higherRadicalFieldOverLower (K := K) e N beta
    let M := higherRadicalActualCompositumField
      (K := K) (L := L) e N beta
    letI : Algebra K K' :=
      ((algebraMap F K').comp (algebraMap K F)).toAlgebra
    letI : Algebra Rₙ K' :=
      higherRadicalFieldOverLowerRootAlgebra
        (e := e) base hN varpi hvarpiPrime beta hbetaPow
    letI : Algebra K' M :=
      higherRadicalActualFactorHigherFieldAlgebra base target beta
    letI : Algebra Rₙ M := actual.rootMap.toAlgebra
    IsScalarTower Rₙ K' M := by
  dsimp only
  let e := ramificationIndex base target
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let F := lowerRadicalField (K := K) e N beta
  let K' := higherRadicalFieldOverLower (K := K) e N beta
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N beta
  let : Algebra K K' :=
    ((algebraMap F K').comp (algebraMap K F)).toAlgebra
  let : Algebra Rₙ K' :=
    higherRadicalFieldOverLowerRootAlgebra
      (e := e) base hN varpi hvarpiPrime beta hbetaPow
  let : Algebra K' M :=
    higherRadicalActualFactorHigherFieldAlgebra base target beta
  let : Algebra Rₙ M := actual.rootMap.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact DFunLike.congr_fun
    (higherRadicalActualFactor_algebraMap_comp_eq_rootMap
      base target hN varpi hvarpiPrime beta hbetaPow actual) x |>.symm

end EtaleFundamentalGroups.Kummer

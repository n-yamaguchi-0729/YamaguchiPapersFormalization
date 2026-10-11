/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.ActualCompositum.TensorComponent

/-!
# Intrinsic coordinates for a fixed higher-radical tensor component

The lower-factor comparison needs positivity of the valuation ramification
index, primality of a chosen uniformizer, and the lower-power coordinate of
the fixed higher root.  All three are intrinsic consequences of the valued
extension and tensor-component data; this file exposes them so no consumer
has to accept them as hypotheses.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- The ramification index of a finite extension of discrete valuation
rings is positive. -/
theorem ramificationIndex_pos_of_moduleFinite
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    0 < ramificationIndex base target := by
  let W := target.valuationSubring
  apply Nat.pos_of_ne_zero
  simpa [ramificationIndex] using
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
      (maximalIdeal_map_integerMap_ne_bot base target)
      (IsLocalRing.maximalIdeal.isMaximal W).isPrime
      (maximalIdeal_map_integerMap_le base target))

/-- A uniformizer in the valuation subring of a discrete valuation field is
a prime element. -/
theorem dvfUniformizer_prime
    {K : Type uK} [Field K]
    (base : DVF.{uK, uV} K)
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K)) :
    Prime varpi := by
  let V := base.valuationSubring
  have hvarpi_ne : varpi ≠ 0 := by
    intro hzero
    apply hvarpi.ne_zero
    exact congrArg Subtype.val hzero
  apply (Ideal.span_singleton_prime hvarpi_ne).mp
  rw [← Valuation.IsUniformizer.is_generator hvarpi]
  exact (IsLocalRing.maximalIdeal.isMaximal V).isPrime

/-- The distinguished root in a fixed pure-radical tensor component keeps
its defining `N`-th power equation after the chosen embedding into the
right field's algebraic closure. -/
theorem fixedTensorComponentEmbeddedRoot_pow
    {K : Type uK} {F : Type uF} {L : Type uL}
    [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L]
    (base : DVF.{uK, uV} K)
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring)
    (hvarpiPrime : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let P := GenericTensorFieldComponent m
    letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
    let beta : AlgebraicClosure L := j rootP
    beta ^ N = algebraMap K (AlgebraicClosure L) (varpi : K) := by
  dsimp only
  let V := base.valuationSubring
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
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
  let beta : AlgebraicClosure L := j rootP
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  have hrootP : rootP ^ N = algebraMap V P varpi :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  calc
    beta ^ N = j (rootP ^ N) := (map_pow j rootP N).symm
    _ = j (algebraMap V P varpi) := by rw [hrootP]
    _ = j (algebraMap K P (varpi : K)) := rfl
    _ = algebraMap K (AlgebraicClosure L) (varpi : K) :=
      (j.restrictScalars K).commutes (varpi : K)

/-- If the actual valuation ramification index divides the prescribed fixed
root exponent, the corresponding lower power of the embedded component root
is the base uniformizer. -/
theorem fixedTensorComponentEmbeddedRoot_lowerPow
    {K : Type uK} {F : Type uF} {L : Type uL}
    [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (hN : 0 < N)
    (varpi : base.valuationSubring)
    (hvarpiPrime : Prime varpi)
    (hdiv : ramificationIndex base target ∣ N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let P := GenericTensorFieldComponent m
    letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
    let beta : AlgebraicClosure L := j rootP
    (beta ^ (N / ramificationIndex base target)) ^
        ramificationIndex base target =
      algebraMap K (AlgebraicClosure L) (varpi : K) := by
  dsimp only
  let V := base.valuationSubring
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
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
  let beta : AlgebraicClosure L := j rootP
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  have hbetaPow : beta ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow base hN varpi hvarpiPrime m
  rw [show (beta ^ (N / ramificationIndex base target)) ^
      ramificationIndex base target =
        beta ^ ((N / ramificationIndex base target) *
          ramificationIndex base target) by simp only [pow_mul]]
  rw [Nat.div_mul_cancel hdiv, hbetaPow]

end EtaleFundamentalGroups.Kummer

end

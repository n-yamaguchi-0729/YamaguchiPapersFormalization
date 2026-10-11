/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.FieldComponent.BaseEquivRightBijective
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactor.LeftBijective

/-!
# Right-coordinate triviality after a fixed higher-radical component

Strict-Henselian retained-factor data identifies every fixed higher-radical
component with its canonical left root field.  Tensoring that literal fixed
component once more over the same root field therefore has no effect on the
right coordinate in any selected second-stage component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW uE

/-- Every second-stage tensor component over a fixed higher-radical
component has its right field as the whole component.

The required bijectivity of the base map is not assumed: it is produced by
`lowerUnitFactorHigherBaseChangeFixedComponent_leftAlgebraMap_bijective`
from the retained factor and then consumed by the generic tensor-collapse
theorem. -/
theorem lowerUnitFactorHigherFixedComponent_secondStageRight_bijective
    {K : Type uK} {Froot : Type uF} {L : Type uL} {E : Type uE}
    [Field K] [Field Froot] [Field L] [Field E]
    [Algebra K Froot] [Algebra K L] [Algebra Froot E]
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
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi (dvfUniformizer_prime base varpi hvarpi) m
      HigherRadicalUnitFactorData base target varpi pi N (j rootP))
    (q : Ideal
      (GenericTensorFieldComponent m ⊗[Froot] E)) [q.IsMaximal] :
    let : Algebra E (GenericTensorFieldComponent q) :=
      genericTensorFieldComponentRightAlgebra q
    Function.Bijective
      (algebraMap E (GenericTensorFieldComponent q)) := by
  intro algebraEQ
  have hleft : Function.Bijective
      (algebraMap Froot (GenericTensorFieldComponent m)) :=
    lowerUnitFactorHigherBaseChangeFixedComponent_leftAlgebraMap_bijective
      (K := K) (Froot := Froot) (L := L)
      base target hN varpi hvarpi hdiv pi m factor
  exact
    genericTensorFieldComponentRight_bijective_of_base_bijective
      (K₀ := Froot) (K₁ := GenericTensorFieldComponent m) (L := E)
      hleft q

end EtaleFundamentalGroups.Kummer

end

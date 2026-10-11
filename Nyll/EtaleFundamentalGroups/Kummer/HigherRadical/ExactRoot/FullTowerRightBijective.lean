/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.Refinement.RightBijective
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.FixedComponent.SecondStageRightBijective
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.FixedTensorComponentBijective

/-!
# Right coordinates in the exact-root full tensor tower

Fix an exact root field for the final right-hand valued field.  A retained
higher-radical factor for another fixed component identifies that component
with the root field on its canonical left coordinate.  Consequently the
actual field tower through that fixed component does not enlarge any further
right-hand tensor component.

For an arbitrary maximal component at the end of the tower, this file uses
its canonical contracted ideal and canonical second-stage ideal.  The exact
root theorem supplies bijectivity at the contracted component, while the
higher-factor theorem supplies it at the second stage.  Tensor refinement
then recovers the original final ideal and preserves the literal right
coordinate.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uOmega uWOmega uL uWL

private theorem finiteDimensional_targetField_fullTower
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uWL} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional K L := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsFractionRing W L := target.valuationSubring_isFractionRing
  let eGeneric : (K ⊗[V] W) ≃ₐ[K] L := finiteGenericFiberAlgEquiv
  let : Module.Finite K (K ⊗[V] W) :=
    Module.Finite.base_change V K W
  exact Module.Finite.equiv eGeneric.toLinearEquiv

/-- Let `Froot` be the exact ramification-root field for `L`.  If the same
root exponent is a higher exponent for `Omega`, a retained unit factor in a
fixed component of `Froot tensor_K Omega` makes that component a genuine
intermediate field which is equivalent to `Froot` on the canonical left
coordinate.  Every maximal final component after tensoring this actual
intermediate field with `L` is then canonically equal to `L` on its right
coordinate.

Neither of the two componentwise bijectivities, nor an equality identifying
the final component with a chosen refinement, is an input: all three are
constructed from the retained factors and the canonical tensor tower. -/
theorem
    lowerUnitFactorExactRootFullTower_finalComponent_rightAlgebraMap_bijective
    {K : Type uK} {Froot : Type uF} {Omega : Type uOmega} {L : Type uL}
    [Field K] [Field Froot] [Field Omega] [Field L]
    [Algebra K Froot] [Algebra K Omega] [Algebra K L]
    (base : DVF.{uK, uV} K)
    (omegaTarget : DVF.{uOmega, uWOmega} Omega)
    (target : DVF.{uL, uWL} L)
    [base.valuation.HasExtension omegaTarget.valuation]
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring
      omegaTarget.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (hdiv : ramificationIndex base omegaTarget ∣
      ramificationIndex base target)
    (piOmega : omegaTarget.valuationSubring)
    (pi : target.valuationSubring)
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base omegaTarget - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base omegaTarget - C varpi)))]
    (mOmega : Ideal (Froot ⊗[K] Omega)) [mOmega.IsMaximal]
    (factorOmega :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra Omega (GenericTensorFieldComponent mOmega) :=
        genericTensorFieldComponentRightAlgebra mOmega
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := ramificationIndex base target) varpi mOmega
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        (ramificationIndex_pos_of_moduleFinite base target)
        varpi (dvfUniformizer_prime base varpi hvarpi) mOmega
      HigherRadicalUnitFactorData base omegaTarget varpi piOmega
        (ramificationIndex base target) (j rootP))
    (m : Ideal
      (GenericTensorFieldComponent mOmega ⊗[K] L)) [m.IsMaximal] :
    let : FiniteDimensional K Omega :=
      finiteDimensional_targetField_fullTower base omegaTarget
    let : IsScalarTower K Froot
        (GenericTensorFieldComponent mOmega) :=
      genericTensorFieldComponent_isScalarTower mOmega
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := Froot)
      (F' := GenericTensorFieldComponent mOmega) (L := L) m
    let : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := Froot)
        (F' := GenericTensorFieldComponent mOmega) (L := L) m
    (
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent n) :=
        genericTensorFieldComponentRightAlgebra n
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := ramificationIndex base target) varpi n
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        (ramificationIndex_pos_of_moduleFinite base target)
        varpi (dvfUniformizer_prime base varpi hvarpi) n
      HigherRadicalUnitFactorData base target varpi pi
        (ramificationIndex base target) (j rootP)) →
      let : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      Function.Bijective
        (algebraMap L (GenericTensorFieldComponent m)) := by
  intro finiteKOmega towerKF n maximalN factor algebraLM
  have hn : Function.Bijective
      (genericTensorFieldComponentRight n) := by
    let : Algebra L (GenericTensorFieldComponent n) :=
      genericTensorFieldComponentRightAlgebra n
    have h :=
      pureRadicalFractionFieldGenericTensorComponent_rightAlgebraMap_bijective_of_exactUnitFactor
        (K := K) (Froot := Froot) (L := L)
        base target varpi hvarpi pi n factor
    change Function.Bijective (genericTensorFieldComponentRight n)
    exact h
  let q := genericTensorTowerSecondIdeal
    (K := K) (F := Froot)
    (F' := GenericTensorFieldComponent mOmega) (L := L) m
  let : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K) (F := Froot)
      (F' := GenericTensorFieldComponent mOmega) (L := L) m
  have hq : Function.Bijective
      (genericTensorFieldComponentRight q) := by
    let : Algebra (GenericTensorFieldComponent n)
        (GenericTensorFieldComponent q) :=
      genericTensorFieldComponentRightAlgebra q
    have h := lowerUnitFactorHigherFixedComponent_secondStageRight_bijective
      (K := K) (Froot := Froot) (L := Omega)
      (E := GenericTensorFieldComponent n)
      base omegaTarget
      (ramificationIndex_pos_of_moduleFinite base target)
      varpi hvarpi hdiv piOmega mOmega factorOmega q
    change Function.Bijective (genericTensorFieldComponentRight q)
    exact h
  have hfinal : Function.Bijective
      (genericTensorFieldComponentRight m) :=
    genericTensorTowerFinalComponentRight_bijective
      (K₀ := K) (K₁ := Froot)
      (F := GenericTensorFieldComponent mOmega) (L := L)
      m hn hq
  change Function.Bijective (genericTensorFieldComponentRight m)
  exact hfinal

end EtaleFundamentalGroups.Kummer

end

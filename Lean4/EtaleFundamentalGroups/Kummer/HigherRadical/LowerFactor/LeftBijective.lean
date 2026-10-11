/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactor.FixedIntegral.QuotientLinear
import EtaleFundamentalGroups.Kummer.HigherRadical.UnitFactor.StrictHenselianTrivial

/-!
# The fixed full component has no extra left-field extension

Strict-Henselian triviality makes the canonical left map into the retained
unit-factor generic fibre bijective.  Passing to its selected quotient and
then through the higher-root-linear fixed-component comparison remains
surjective.  Since the source is a field, the resulting map is also
injective.  Fraction-ring uniqueness identifies it with the canonical left
map into the fixed full component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- Under the strict-Henselian retained-factor hypotheses, the canonical
left map from the higher radical fraction field to every fixed full tensor
component is bijective. -/
theorem lowerUnitFactorHigherBaseChangeFixedComponent_leftAlgebraMap_bijective
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
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
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :
    Function.Bijective
      (algebraMap Froot (GenericTensorFieldComponent m)) := by
  let V := base.valuationSubring
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let rootP : P := pureRadicalFractionFieldGenericTensorComponentRoot
    (N := N) varpi m
  let hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  let e := ramificationIndex base target
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let Fₑ : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  let : Algebra Fₑ K' := K'.algebra
  let : Algebra K K' :=
    ((algebraMap Fₑ K').comp (algebraMap K Fₑ)).toAlgebra
  have hbetaPow : beta ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow
      base hN varpi hvarpiPrime m
  let : Algebra Rₙ K' :=
    higherRadicalFieldOverLowerRootAlgebra
      (e := e) base hN varpi hvarpiPrime beta hbetaPow
  let higherRootMap : Rₑ →ₐ[V] Rₙ :=
    adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let Tₙ := Rₙ ⊗[Rₑ] Cq
  let : Algebra Rₙ Tₙ := Algebra.TensorProduct.leftAlgebra
  let : Algebra Rₑ Froot :=
    ((algebraMap Rₙ Froot).comp (algebraMap Rₑ Rₙ)).toAlgebra
  let : IsScalarTower Rₑ Rₙ Froot :=
    IsScalarTower.of_algebraMap_eq' rfl
  let halphaPow : alpha ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_lowerPow
      base target hN varpi hvarpiPrime hdiv m
  let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] Fₑ :=
    pureRadicalGenericFiberAlgEquiv
      (ramificationIndex_pos_of_moduleFinite base target)
      varpi hvarpiPrime alpha halphaPow
  let : Algebra Rₑ Fₑ :=
    (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
  let : Algebra Rₑ K' :=
    ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
  let : IsScalarTower Rₑ Rₙ K' :=
    higherRadicalFieldOverLower_root_isScalarTower
      base (ramificationIndex_pos_of_moduleFinite base target) hN hdiv
        varpi hvarpiPrime beta hbetaPow
  let G := Froot ⊗[Rₙ] Tₙ
  let : CommRing G := inferInstance
  let J : Ideal G := lowerUnitFactorHigherBaseChangeFixedComponentIdeal
    base target hN varpi hvarpi hdiv pi m factor
  let : Algebra Rₙ P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
  let componentEquiv : (G ⧸ J) ≃ₐ[Rₙ] P :=
    lowerUnitFactorHigherBaseChangeFixedComponentAlgEquiv
      base target hN varpi hvarpi hdiv pi m factor
  let inF : Froot →ₐ[Rₙ] G := Algebra.TensorProduct.includeLeft
  let qmk : G →ₐ[Rₙ] (G ⧸ J) := Ideal.Quotient.mkₐ Rₙ J
  let toP : Froot →+* P :=
    componentEquiv.toRingHom.comp (qmk.toRingHom.comp inF.toRingHom)
  have hinF : Function.Bijective inF :=
    higherRadicalUnitFactorData_higherGenericFiber_includeLeft_bijective
      base target varpi pi N hdiv beta factor
  have htoPSurjective : Function.Surjective toP :=
    componentEquiv.surjective.comp
      (Ideal.Quotient.mk_surjective.comp hinF.surjective)
  have htoP : toP = algebraMap Froot P := by
    apply IsFractionRing.ringHom_ext (A := Rₙ)
    intro z
    calc
      toP (algebraMap Rₙ Froot z) =
          componentEquiv
            (qmk (inF (algebraMap Rₙ Froot z))) := rfl
      _ = componentEquiv (qmk (algebraMap Rₙ G z)) := by
        rw [inF.commutes]
      _ = componentEquiv (algebraMap Rₙ (G ⧸ J) z) := by
        rw [qmk.commutes]
      _ = algebraMap Rₙ P z := componentEquiv.commutes z
      _ = algebraMap Froot P (algebraMap Rₙ Froot z) :=
        rfl
  rw [← htoP]
  exact ⟨toP.injective, htoPSurjective⟩

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactor.FixedIntegral.Quotient
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactor.FixedIntegral.Linear
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.ActualFactorTower

/-!
# Higher-root linearity of the fixed integral component quotient

The fixed quotient comparison is assembled from the higher-root-linear
generic-fibre comparison, the canonical lower-factor quotient comparison,
and the actual-compositum comparison.  The scalar tower through the embedded
higher radical field makes the middle comparison linear over the full higher
root ring.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- An actual algebra equivalence identifies quotients by a contracted ideal.
The image equality is computed from surjectivity and the supplied contraction equality. -/
private noncomputable def quotientAlgEquivOfComap
    {R : Type*} {A : Type*} {B : Type*}
    [CommSemiring R] [CommRing A] [CommRing B]
    {algRA : Algebra R A} {algRB : Algebra R B} :
    let : Algebra R A := algRA
    let : Algebra R B := algRB
    (e : A ≃ₐ[R] B) → (J : Ideal A) → (I : Ideal B) →
    (J = I.comap e.toRingHom) → (A ⧸ J) ≃ₐ[R] (B ⧸ I) := by
  intro algebraRA algebraRB e J I hJ
  have hIJ : I = J.map e.toRingHom :=
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective I).symm.trans
      (congrArg (Ideal.map e.toRingHom) hJ.symm)
  exact Ideal.quotientEquivAlg J I e hIJ

private noncomputable def fixedIntegralQuotientComparison
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [Field Froot] [Field L]
    [Algebra K Froot] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
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
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :=
  let V := base.valuationSubring
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V := base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let rootP := pureRadicalFractionFieldGenericTensorComponentRoot (N := N) varpi m
  let hvarpiPrime := dvfUniformizer_prime base varpi hvarpi
  let j := pureRadicalFractionFieldGenericTensorComponentEmbedding hN varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  let halphaPow := fixedTensorComponentEmbeddedRoot_lowerPow
    base target hN varpi hvarpiPrime hdiv m
  let eLinear := lowerUnitFactorHigherBaseChangeGenericFiberAlgEquiv
    base target hN varpi hvarpi hdiv pi m factor
  let J := lowerUnitFactorHigherBaseChangeFixedComponentIdeal
    base target hN varpi hvarpi hdiv pi m factor
  let I := lowerUnitFactorHigherGenericComponentIdeal
    base target varpi pi N beta
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  have hJ : I.comap eLinear.toRingHom = J := by
    dsimp only [J, lowerUnitFactorHigherBaseChangeFixedComponentIdeal,
      lowerUnitFactorHigherBaseChangeGenericFiberRingEquiv, eLinear]
  let quotientFromLinear := quotientAlgEquivOfComap eLinear
  quotientFromLinear J I hJ.symm

private noncomputable def fixedIntegralLowerComponentComparison
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
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :=
  let V := base.valuationSubring
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V := base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let : Algebra Rₑ Cq := factor.radicalToUnitFactor.toRingHom.toAlgebra
  let : Algebra Rₙ P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra (K := K) varpi m
  let : FiniteDimensional K Froot :=
    pureRadicalFractionField_finiteDimensional
      hN varpi (dvfUniformizer_prime base varpi hvarpi)
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P := pureRadicalFractionFieldGenericTensorComponentRoot
    (N := N) varpi m
  let hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Fₑ : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N beta
  let : Algebra Fₑ K' := K'.algebra
  let : Algebra K K' :=
    ((algebraMap Fₑ K').comp (algebraMap K Fₑ)).toAlgebra
  let hbetaPow : beta ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow
      base hN varpi hvarpiPrime m
  let : Algebra Rₙ K' :=
    higherRadicalFieldOverLowerRootAlgebra
      (e := e) base hN varpi hvarpiPrime beta hbetaPow
  let halphaPow : alpha ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_lowerPow
      base target hN varpi hvarpiPrime hdiv m
  let : Algebra V Fₑ :=
    ((algebraMap K Fₑ).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K Fₑ := IsScalarTower.of_algebraMap_eq' rfl
  let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] Fₑ :=
    pureRadicalGenericFiberAlgEquiv
      (ramificationIndex_pos_of_moduleFinite base target)
      varpi hvarpiPrime alpha halphaPow
  let : Algebra Rₑ Fₑ :=
    (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
  let : Algebra Rₑ K' :=
    ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
  let H := K' ⊗[Rₑ] Cq
  let : Algebra Rₙ H :=
    ((Algebra.TensorProduct.includeLeftRingHom
      (R := Rₑ) (A := K') (B := Cq)).comp
        (algebraMap Rₙ K')).toAlgebra
  let I : Ideal H := lowerUnitFactorHigherGenericComponentIdeal
    base target varpi pi N beta
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  let actual : HigherRadicalActualFactorData base target varpi N beta :=
    Classical.choice (higherRadicalActualFactorData_of_unitFactorData
      base target varpi hvarpi pi N hdiv beta hbetaPow factor)
  let : Algebra K' M :=
    higherRadicalActualFactorHigherFieldAlgebra base target beta
  let : Algebra Rₙ M :=
    higherRadicalActualFactorDataAlgebra base target varpi beta actual
  let : IsScalarTower Rₙ K' M :=
    higherRadicalActualFactor_isScalarTower
      base target hN varpi hvarpiPrime beta hbetaPow actual
  let : Algebra K' H := Algebra.TensorProduct.leftAlgebra
  let : Algebra K' (H ⧸ I) := Ideal.Quotient.algebra K'
  let towerRnKprimeQuotient := IsScalarTower.of_algebraMap_eq'
    (R := Rₙ) (S := K') (A := H ⧸ I) (by
      apply RingHom.ext
      intro z
      rfl)
  let lowerEquiv : (H ⧸ I) ≃ₐ[K'] M :=
    lowerUnitFactorHigherGenericComponentAlgEquiv
      base target varpi pi N beta
        (ramificationIndex_pos_of_moduleFinite base target)
        hvarpiPrime halphaPow factor
  let lowerEquivLinear : (H ⧸ I) ≃ₐ[Rₙ] M := lowerEquiv.restrictScalars Rₙ
  let basePAlgebra : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : SMul V P := basePAlgebra.toSMul
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  let higherEquiv : M ≃ₐ[Rₙ] P :=
    higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv
      base target hN varpi hvarpiPrime m actual
  lowerEquivLinear.trans higherEquiv

/-- The fixed integral component quotient is the selected actual-compositum
tensor component as an algebra over the full higher root ring. -/
noncomputable def lowerUnitFactorHigherBaseChangeFixedComponentAlgEquiv
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
    let V := base.valuationSubring
    let P := GenericTensorFieldComponent m
    let : IsDiscreteValuationRing V := base.valuationSubring_isDiscreteValuationRing
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[V] Rₙ := adjoinRootPowerMapOfDvd hdiv varpi
    let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    let : Algebra Rₑ Cq := factor.radicalToUnitFactor.toRingHom.toAlgebra
    let Tₙ := Rₙ ⊗[Rₑ] Cq
    let : Algebra Rₙ Tₙ := Algebra.TensorProduct.leftAlgebra
    let G := Froot ⊗[Rₙ] Tₙ
    let : CommRing G := inferInstance
    let J : Ideal G := lowerUnitFactorHigherBaseChangeFixedComponentIdeal
      base target hN varpi hvarpi hdiv pi m factor
    let : Algebra Rₙ P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra (K := K) varpi m
    (G ⧸ J) ≃ₐ[Rₙ] P := by
  intro V P hDVR hFrac e Rₑ Rₙ Cq higherRootMap algReRn algReCq Tₙ algRnTn G ringG J algRnP
  let compose
      {R : Type uK} {A : Type (max uF uK uL)} {B : Type uL} {C : Type (max uF uL)}
      [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
      {algRA : Algebra R A} {algRB : Algebra R B} {algRC : Algebra R C} :
      let : Algebra R A := algRA
      let : Algebra R B := algRB
      let : Algebra R C := algRC
      (A ≃ₐ[R] B) → (B ≃ₐ[R] C) → (A ≃ₐ[R] C) := by
    intro algebraRA algebraRB algebraRC left right
    exact left.trans right
  exact compose
    (fixedIntegralQuotientComparison base target hN varpi hvarpi hdiv pi m factor)
    (fixedIntegralLowerComponentComparison base target hN varpi hvarpi hdiv pi m factor)

end EtaleFundamentalGroups.Kummer

end

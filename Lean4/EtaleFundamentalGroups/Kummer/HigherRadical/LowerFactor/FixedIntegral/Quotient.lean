/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactor.FixedIntegral.Basic

/-!
# The retained lower factor in the fixed integral generic component

The generic fibre of the literal higher base change of the retained lower
unit factor is identified with the lower tensor product used to choose the
fixed higher component.  Pulling the already chosen maximal ideal back along
that identification gives the corresponding component of the literal
integral base change; its quotient is the fixed higher tensor component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW
universe uG uH uP

private noncomputable def quotientRingEquivOfRingEquiv
    {G : Type uG} {H : Type uH} {P : Type uP}
    [CommRing G] [CommRing H] [CommRing P]
    (E : G ≃+* H) (I : Ideal H) (h : (H ⧸ I) ≃+* P) :
    (G ⧸ I.comap E.toRingHom) ≃+* P := by
  let J := I.comap E.toRingHom
  have hIJ : I = J.map E.toRingHom :=
    (Ideal.map_comap_of_surjective E.toRingHom E.surjective I).symm
  exact (Ideal.quotientEquiv J I E hIJ).trans h

/-- Transporting a root into the pulled-back quotient and then through the
quotient comparison returns its original image.  This calculation justifies
using the computed image in `lowerUnitFactorHigherBaseChangeFixedComponentRoot`. -/
private theorem quotientComponentRoot_eq
    {G : Type uG} {H : Type uH} {P : Type uP}
    [CommRing G] [CommRing H] [CommRing P]
    (E : G ≃+* H) (I : Ideal H) (h : (H ⧸ I) ≃+* P) (c : H) :
    let J := I.comap E.toRingHom
    let hIJ : I = J.map E.toRingHom :=
      (Ideal.map_comap_of_surjective E.toRingHom E.surjective I).symm
    let qE : (G ⧸ J) ≃+* (H ⧸ I) := Ideal.quotientEquiv J I E hIJ
    (qE.trans h) (qE.symm (Ideal.Quotient.mk I c)) =
      h (Ideal.Quotient.mk I c) := by
  intro J hIJ qE
  exact congrArg h (qE.apply_symm_apply (Ideal.Quotient.mk I c))

/-- The component ideal of the literal higher base change of the same lower
unit factor `Cq`, selected by the fixed higher tensor component `m`. -/
noncomputable def lowerUnitFactorHigherBaseChangeFixedComponentIdeal
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
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[V] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let Tₙ := Rₙ ⊗[Rₑ] Cq
    let : Algebra Rₙ Tₙ := Algebra.TensorProduct.leftAlgebra
    Ideal (Froot ⊗[Rₙ] Tₙ) := by
  intro V e Rₑ Rₙ Cq higherRootMap algReRn algReCq Tₙ algRnTn
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
    (N := N) varpi m
  let hvarpiPrime := dvfUniformizer_prime base varpi hvarpi
  let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
    hN varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Fₑ : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  let : Algebra Fₑ K' := K'.algebra
  let : Algebra K K' :=
    ((algebraMap Fₑ K').comp (algebraMap K Fₑ)).toAlgebra
  let : Algebra Rₙ K' :=
    higherRadicalFieldOverLowerRootAlgebra
      (e := e) base hN varpi hvarpiPrime beta
        (fixedTensorComponentEmbeddedRoot_pow
          base hN varpi hvarpiPrime m)
  let : Algebra Rₑ Froot :=
    ((algebraMap Rₙ Froot).comp (algebraMap Rₑ Rₙ)).toAlgebra
  let : IsScalarTower Rₑ Rₙ Froot :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra V Fₑ :=
    ((algebraMap K Fₑ).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K Fₑ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Rₑ Fₑ :=
    (genericFiberRightAlgHom
      (pureRadicalGenericFiberAlgEquiv
        (ramificationIndex_pos_of_moduleFinite base target)
        varpi hvarpiPrime alpha
        (fixedTensorComponentEmbeddedRoot_lowerPow
          base target hN varpi hvarpiPrime hdiv m))).toRingHom.toAlgebra
  let : Algebra Rₑ K' :=
    ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
  let : IsScalarTower Rₑ Rₙ K' :=
    higherRadicalFieldOverLower_root_isScalarTower
      base (ramificationIndex_pos_of_moduleFinite base target) hN hdiv
        varpi hvarpiPrime beta
        (fixedTensorComponentEmbeddedRoot_pow
          base hN varpi hvarpiPrime m)
  let halphaPow : alpha ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_lowerPow
      base target hN varpi hvarpiPrime hdiv m
  let E : (Froot ⊗[Rₙ] Tₙ) ≃+* (K' ⊗[Rₑ] Cq) :=
    lowerUnitFactorHigherBaseChangeGenericFiberRingEquiv
    base target hN varpi hvarpi hdiv pi m factor
  let I : Ideal (K' ⊗[Rₑ] Cq) := lowerUnitFactorHigherGenericComponentIdeal
    base target varpi pi N beta
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  exact I.comap E.toRingHom

/-- The pulled-back ideal is maximal, so it is the literal generic component
of the higher base change corresponding to the already fixed component `m`. -/
theorem lowerUnitFactorHigherBaseChangeFixedComponentIdeal_isMaximal
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
      HigherRadicalUnitFactorData base target varpi pi N (j rootP)) :
    let V := base.valuationSubring
    let P := GenericTensorFieldComponent m
    let : IsDiscreteValuationRing V :=
      base.valuationSubring_isDiscreteValuationRing
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let : Algebra L P := genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let hvarpiPrime := dvfUniformizer_prime base varpi hvarpi
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
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
    let : Algebra Rₙ K' :=
      higherRadicalFieldOverLowerRootAlgebra
        (e := e) base hN varpi hvarpiPrime beta
          (fixedTensorComponentEmbeddedRoot_pow
            base hN varpi hvarpiPrime m)
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
    let : Algebra V Fₑ :=
      ((algebraMap K Fₑ).comp (algebraMap V K)).toAlgebra
    let : IsScalarTower V K Fₑ := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra Rₑ Fₑ :=
      (genericFiberRightAlgHom
        (pureRadicalGenericFiberAlgEquiv
          (ramificationIndex_pos_of_moduleFinite base target)
          varpi hvarpiPrime alpha
          (fixedTensorComponentEmbeddedRoot_lowerPow
            base target hN varpi hvarpiPrime hdiv m))).toRingHom.toAlgebra
    let : Algebra Rₑ K' :=
      ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
    let : IsScalarTower Rₑ Rₙ K' :=
      higherRadicalFieldOverLower_root_isScalarTower
        base (ramificationIndex_pos_of_moduleFinite base target) hN hdiv
          varpi hvarpiPrime beta
          (fixedTensorComponentEmbeddedRoot_pow
            base hN varpi hvarpiPrime m)
    (lowerUnitFactorHigherBaseChangeFixedComponentIdeal
      base target hN varpi hvarpi hdiv pi m factor).IsMaximal := by
  intro V P hDVR hFrac algLP rootP hvarpiPrime j beta e alpha Rₑ Rₙ Cq Fₑ K'
    algFeKprime algKKprime algRnKprime higherRootMap algReRn algReCq Tₙ
    algRnTn algReFroot towerReRnFroot algVFe towerVKFe algReFe algReKprime
    towerReRnKprime
  let halphaPow : alpha ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_lowerPow
      base target hN varpi hvarpiPrime hdiv m
  let E : (Froot ⊗[Rₙ] Tₙ) ≃+* (K' ⊗[Rₑ] Cq) :=
    lowerUnitFactorHigherBaseChangeGenericFiberRingEquiv
    base target hN varpi hvarpi hdiv pi m factor
  let I : Ideal (K' ⊗[Rₑ] Cq) := lowerUnitFactorHigherGenericComponentIdeal
    base target varpi pi N beta
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  have hI : I.IsMaximal :=
    lowerUnitFactorHigherGenericComponentIdeal_isMaximal
      base target varpi pi N beta
        (ramificationIndex_pos_of_moduleFinite base target)
        hvarpiPrime halphaPow factor
  exact hI.comap_bijective E.toRingHom E.bijective

/-- The quotient of the literal higher base change at the pulled-back
component is the fixed higher tensor component.  The construction uses the
same maximal ideal and the same lower unit factor as the local comparison. -/
opaque
    lowerUnitFactorHigherBaseChangeFixedComponentRingEquiv
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
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[V] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let Tₙ := Rₙ ⊗[Rₑ] Cq
    let : Algebra Rₙ Tₙ := Algebra.TensorProduct.leftAlgebra
    let G := Froot ⊗[Rₙ] Tₙ
    let : CommRing G := inferInstance
    let J : Ideal G := lowerUnitFactorHigherBaseChangeFixedComponentIdeal
      base target hN varpi hvarpi hdiv pi m factor
    (G ⧸ J) ≃+* P := by
  intro V P e Rₑ Rₙ Cq higherRootMap algReRn algReCq Tₙ algRnTn G hCommG J
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
    (N := N) varpi m
  let hvarpiPrime := dvfUniformizer_prime base varpi hvarpi
  let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
    hN varpi hvarpiPrime m
  let beta : AlgebraicClosure L := j rootP
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Fₑ : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  let : Algebra Fₑ K' := K'.algebra
  let : Algebra V Fₑ :=
    ((algebraMap K Fₑ).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K Fₑ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Rₑ Fₑ :=
    (genericFiberRightAlgHom
      (pureRadicalGenericFiberAlgEquiv
        (ramificationIndex_pos_of_moduleFinite base target)
        varpi hvarpiPrime alpha
        (fixedTensorComponentEmbeddedRoot_lowerPow
          base target hN varpi hvarpiPrime hdiv m))).toRingHom.toAlgebra
  let : Algebra Rₑ K' :=
    ((algebraMap Fₑ K').comp (algebraMap Rₑ Fₑ)).toAlgebra
  let halphaPow : alpha ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_lowerPow
      base target hN varpi hvarpiPrime hdiv m
  let H := K' ⊗[Rₑ] Cq
  let : CommRing H := inferInstance
  let E : G ≃+* H := lowerUnitFactorHigherBaseChangeGenericFiberRingEquiv
    base target hN varpi hvarpi hdiv pi m factor
  let I : Ideal H := lowerUnitFactorHigherGenericComponentIdeal
    base target varpi pi N beta
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  have hJ : J = I.comap E.toRingHom := by
    rfl
  let eJ : (G ⧸ J) ≃+* (G ⧸ I.comap E.toRingHom) := Ideal.quotEquivOfEq hJ
  let fixedE : (H ⧸ I) ≃+* P :=
    lowerUnitFactorHigherGenericComponentFixedTensorComponentRingEquiv
      base target hN varpi hvarpi hdiv pi m
        (ramificationIndex_pos_of_moduleFinite base target)
        hvarpiPrime halphaPow factor
  let result := quotientRingEquivOfRingEquiv E I fixedE
  exact eJ.trans result

/-- The element of the fixed component represented by the distinguished
root of the literal retained lower factor.

The original quotient transport sends `qE.symm (Ideal.Quotient.mk I rootC)`
through `qE.trans fixedE`.  The calculation `quotientComponentRoot_eq` shows
that its image is exactly `fixedE (Ideal.Quotient.mk I rootC)`, used here. -/
noncomputable def lowerUnitFactorHigherBaseChangeFixedComponentRoot
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
    GenericTensorFieldComponent m := by
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
  let Cq := AdjoinRoot factor.q
  let Fₑ : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let K' : IntermediateField Fₑ (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  let : Algebra Fₑ K' := K'.algebra
  let : Algebra K K' :=
    ((algebraMap Fₑ K').comp (algebraMap K Fₑ)).toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
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
  let I : Ideal H := lowerUnitFactorHigherGenericComponentIdeal
    base target varpi pi N beta
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  let fixedE : (H ⧸ I) ≃+* P :=
    lowerUnitFactorHigherGenericComponentFixedTensorComponentRingEquiv
      base target hN varpi hvarpi hdiv pi m
        (ramificationIndex_pos_of_moduleFinite base target)
        hvarpiPrime halphaPow factor
  let rootC : H :=
    (1 : K') ⊗ₜ[Rₑ] AdjoinRoot.root factor.q
  exact fixedE (Ideal.Quotient.mk I rootC)

/-- The fixed integral component comparison retains the distinguished root
of the original lower unit factor.  After the chosen embedding of the fixed
component, that root is literally the unit-absorption coordinate `delta`. -/
theorem lowerUnitFactorHigherBaseChangeFixedComponentRingEquiv_root
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
    let P := GenericTensorFieldComponent m
    let : IsDiscreteValuationRing base.valuationSubring :=
      base.valuationSubring_isDiscreteValuationRing
    let : IsFractionRing base.valuationSubring K :=
      base.valuationSubring_isFractionRing
    let : Algebra L P := genericTensorFieldComponentRightAlgebra m
    let hvarpiPrime := dvfUniformizer_prime base varpi hvarpi
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
    j (lowerUnitFactorHigherBaseChangeFixedComponentRoot
      base target hN varpi hvarpi hdiv pi m factor) = factor.delta := by
  intro P hDVR hFrac algLP hvarpiPrime j
  have halphaPow := fixedTensorComponentEmbeddedRoot_lowerPow
    base target hN varpi hvarpiPrime hdiv m
  have hFixed := lowerUnitFactorHigherGenericComponentFixedTensorComponentRingEquiv_root
    base target hN varpi hvarpi hdiv pi m
      (ramificationIndex_pos_of_moduleFinite base target)
      hvarpiPrime halphaPow factor
  exact hFixed

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.FieldOverLowerFractionRing
import EtaleFundamentalGroups.Kummer.HigherRadical.LowerFactor.FixedTensor
import EtaleFundamentalGroups.Kummer.HigherRadical.UnitFactorFiniteEtale

/-!
# A retained lower unit factor in the fixed higher integral component

The same `Cq` selected by unit absorption is finite etale over the actual
root ring and remains so after the auxiliary higher root base change.  Here
we identify the generic fibre of that literal base change with the lower
tensor product whose canonical quotient was already identified with a fixed
higher tensor component.  No second unit factor or field component is chosen.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

universe uR uS uE uC

/-- Cancellation of a base change followed by a scalar equivalence remains
linear over the intermediate scalar ring.  The action on the target tensor
product is the literal action through its left factor. -/
private noncomputable def cancelBaseChangeCongrAlgEquiv
    {R : Type uR} {S : Type uS} {F : Type uF}
    {E : Type uE} {C : Type uC}
    [CommRing R] [CommRing S] [CommRing F] [CommRing E] [CommRing C]
    [Algebra R S] [Algebra R C]
    [Algebra S F] [Algebra R F] [IsScalarTower R S F]
    [Algebra S E] [Algebra R E] [IsScalarTower R S E]
    (e : F ≃ₐ[S] E) :
    let T := S ⊗[R] C
    let : Algebra S T := Algebra.TensorProduct.leftAlgebra
    let G := F ⊗[S] T
    let H := E ⊗[R] C
    let : Algebra S H :=
      ((Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := E) (B := C)).comp (algebraMap S E)).toAlgebra
    G ≃ₐ[S] H := by
  intro T algST G H algSH
  let M := F ⊗[R] C
  let : Algebra S M :=
    ((Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := F) (B := C)).comp (algebraMap S F)).toAlgebra
  let eCancel : G ≃ₐ[F] M :=
    Algebra.TensorProduct.cancelBaseChange R S F F C
  let eCancelS : G ≃ₐ[S] M :=
    { toRingEquiv := eCancel.toRingEquiv
      commutes' := by
        intro x
        change eCancel (algebraMap F G (algebraMap S F x)) =
          algebraMap F M (algebraMap S F x)
        exact eCancel.commutes (algebraMap S F x) }
  let eTensor : M ≃ₐ[R] H :=
    Algebra.TensorProduct.congr
      (e.restrictScalars R) (AlgEquiv.refl : C ≃ₐ[R] C)
  let eTensorS : M ≃ₐ[S] H :=
    { toRingEquiv := eTensor.toRingEquiv
      commutes' := by
        intro x
        change eTensor
            ((Algebra.TensorProduct.includeLeft : F →ₐ[R] M)
              (algebraMap S F x)) =
          (Algebra.TensorProduct.includeLeft : E →ₐ[R] H)
            (algebraMap S E x)
        change eTensor ((algebraMap S F x) ⊗ₜ[R] (1 : C)) =
          (algebraMap S E x) ⊗ₜ[R] (1 : C)
        change (Algebra.TensorProduct.congr
            (e.restrictScalars R) (AlgEquiv.refl : C ≃ₐ[R] C))
              ((algebraMap S F x) ⊗ₜ[R] (1 : C)) =
          (algebraMap S E x) ⊗ₜ[R] (1 : C)
        calc
          _ = (e.restrictScalars R) (algebraMap S F x) ⊗ₜ[R]
                (AlgEquiv.refl : C ≃ₐ[R] C) 1 :=
            Algebra.TensorProduct.map_tmul
              (e.restrictScalars R : F →ₐ[R] E)
              (AlgHom.id R C) (algebraMap S F x) 1
          _ = (algebraMap S E x) ⊗ₜ[R] (1 : C) := by
            change e (algebraMap S F x) ⊗ₜ[R] (1 : C) =
              (algebraMap S E x) ⊗ₜ[R] (1 : C)
            rw [e.commutes] }
  exact
    { toRingEquiv := eCancel.toRingEquiv.trans eTensor.toRingEquiv
      commutes' := fun x ↦
        (congrArg eTensor (eCancelS.commutes x)).trans (eTensorS.commutes x) }


/-- The generic fibre of the literal higher base change of the retained
lower factor, as an equivalence over the prescribed higher root ring.

The higher-root action on the target tensor product is the map through its
`K'` left factor.  Thus this is the linear refinement of
`lowerUnitFactorHigherBaseChangeGenericFiberRingEquiv`. -/
noncomputable def lowerUnitFactorHigherBaseChangeGenericFiberAlgEquiv
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
    let hbetaPow : beta ^ N =
        algebraMap K (AlgebraicClosure L) (varpi : K) :=
      fixedTensorComponentEmbeddedRoot_pow base hN varpi hvarpiPrime m
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
          varpi hvarpiPrime beta hbetaPow
    let G := Froot ⊗[Rₙ] Tₙ
    let H := K' ⊗[Rₑ] Cq
    let : Algebra Rₙ H :=
      ((Algebra.TensorProduct.includeLeftRingHom
        (R := Rₑ) (A := K') (B := Cq)).comp
          (algebraMap Rₙ K')).toAlgebra
    G ≃ₐ[Rₙ] H := by
  intro V P hDVR hFrac algLP rootP hvarpiPrime j beta e alpha Rₑ Rₙ Cq Fₑ K'
    algFeKprime algKKprime hbetaPow algRnKprime higherRootMap algReRn algReCq Tₙ
    algRnTn algReFroot towerReRnFroot algVFe towerVKFe algReFe algReKprime
    towerReRnKprime G H algRnH
  let eFrac : Froot ≃ₐ[Rₙ] K' :=
    higherRadicalFractionFieldAlgEquivHigherField
      (e := e) base hN varpi hvarpiPrime beta hbetaPow
  exact cancelBaseChangeCongrAlgEquiv
    (R := Rₑ) (S := Rₙ) (F := Froot) (E := K') (C := Cq) eFrac


/-- The generic fibre of the literal higher base change of `Cq` is the
same lower-factor tensor product used to select the fixed component `m`.

The first equivalence is cancellation of the integral base change.  The
second transports the chosen fraction field of the higher root ring to the
embedded higher radical field, retaining the lower-root scalar action. -/
noncomputable def lowerUnitFactorHigherBaseChangeGenericFiberRingEquiv
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
    let D := K' ⊗[Rₑ] Cq
    let : CommRing D := Algebra.TensorProduct.instCommRing
    (Froot ⊗[Rₙ] Tₙ) ≃+* D := by
  intro V P hDVR hFrac algLP rootP hvarpiPrime j beta e alpha Rₑ Rₙ Cq Fₑ K'
    algFeKprime algKKprime higherRootMap algReRn algReCq Tₙ algRnTn algReFroot
    towerReRnFroot algVFe towerVKFe algReFe algReKprime D ringD
  have hbetaPow : beta ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow base hN varpi hvarpiPrime m
  let : Algebra Rₙ K' := higherRadicalFieldOverLowerRootAlgebra
    (e := e) base hN varpi hvarpiPrime beta hbetaPow
  let : Algebra Rₙ D :=
    ((Algebra.TensorProduct.includeLeftRingHom
      (R := Rₑ) (A := K') (B := Cq)).comp (algebraMap Rₙ K')).toAlgebra
  let linear := lowerUnitFactorHigherBaseChangeGenericFiberAlgEquiv
    base target hN varpi hvarpi hdiv pi m factor
  let result := linear.toRingEquiv
  exact result

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Henselian.UniformizerDecomposition
import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.ExactRoot.FullTowerRightBijective
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponent.FieldBijectiveExponentUnit
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.OfFieldTower

/-!
# Produced field comparisons for the full-root exponent obstruction

The full-root exponent obstruction previously accepted bijectivity of the
right coordinate in a fixed generic tensor component.  This file constructs
that comparison from the actual exact-root field inside the full field.

The multiplication component of `Froot ⊗[K] Kfull` is selected by its
canonical kernel.  Both retained unit factors are then produced from chosen
uniformizers and the DVR uniformizer decomposition.  Finally the component
comparison is transported through the literal tensor map from its quotient
field back to `Kfull`; no component equality or field-bijectivity proposition
is an input.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uA uK uV uFull uWFull uL uWL uF

private theorem finiteDimensional_targetField_produced
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

/-- An exact root field acting on an actual full field produces the canonical
right-coordinate comparison in every final tensor component.

The multiplication kernel in `Froot ⊗[K] Kfull`, the corresponding
quotient equivalence, the two target uniformizers and decompositions, both
`HigherRadicalUnitFactorData` values, the pulled-back final ideal, and the
coordinate-preserving quotient comparison are all constructed internally. -/
theorem
    exactHigherRootFullField_finalComponent_rightAlgebraMap_bijective
    {K : Type uK} {Froot : Type uF}
    {Kfull : Type uFull} {L : Type uL}
    [Field K] [Field Froot] [Field Kfull] [Field L]
    [Algebra K Froot] [Algebra K Kfull] [Algebra K L]
    [Algebra Froot Kfull] [IsScalarTower K Froot Kfull]
    (base : DVF.{uK, uV} K)
    (fullTarget : DVF.{uFull, uWFull} Kfull)
    (target : DVF.{uL, uWL} L)
    [base.valuation.HasExtension fullTarget.valuation]
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring
      fullTarget.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ)
    (hExact : ramificationIndex base target = N)
    (hdiv : ramificationIndex base fullTarget ∣ N)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing (AdjoinRoot (X ^ N - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField (AdjoinRoot (X ^ N - C varpi)))]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base fullTarget - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base fullTarget - C varpi)))]
    (m : Ideal (Kfull ⊗[K] L)) [m.IsMaximal] :
    let : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    Function.Bijective
      (algebraMap L (GenericTensorFieldComponent m)) := by
  subst N
  intro algebraLM
  let V := base.valuationSubring
  let e := ramificationIndex base target
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiPrime : Prime varpi :=
    dvfUniformizer_prime base varpi hvarpi
  let mFull : Ideal (Froot ⊗[K] Kfull) :=
    fieldTowerTensorComponentIdeal
      (K := K) (K' := Froot) (L := Kfull)
  let : mFull.IsMaximal :=
    fieldTowerTensorComponentIdeal_isMaximal
      (K := K) (K' := Froot) (L := Kfull)
  let eFull : GenericTensorFieldComponent mFull ≃ₐ[Froot] Kfull :=
    fieldTowerTensorComponentAlgEquiv
      (K := K) (K' := Froot) (L := Kfull)
  let : Algebra K (GenericTensorFieldComponent mFull) := inferInstance
  let : IsScalarTower K Froot
      (GenericTensorFieldComponent mFull) :=
    genericTensorFieldComponent_isScalarTower mFull
  let : Algebra Kfull (GenericTensorFieldComponent mFull) :=
    genericTensorFieldComponentRightAlgebra mFull
  obtain ⟨piFull, hpiFull⟩ := fullTarget.exists_uniformizer
  obtain ⟨unitFull, hdecompFull⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base fullTarget hvarpi hpiFull
  let rootFull : GenericTensorFieldComponent mFull :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := e) varpi mFull
  let jFull : GenericTensorFieldComponent mFull →ₐ[Kfull]
      AlgebraicClosure Kfull :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      he varpi hvarpiPrime mFull
  let betaFull : AlgebraicClosure Kfull := jFull rootFull
  have hbetaFull : betaFull ^ e =
      algebraMap K (AlgebraicClosure Kfull) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow
      base he varpi hvarpiPrime mFull
  obtain ⟨factorFull⟩ :=
    higherRadicalUnitFactorData
      base fullTarget varpi hvarpi piFull unitFull hpiFull hdecompFull
      e hdiv betaFull hbetaFull
  let tensorMap :
      (GenericTensorFieldComponent mFull ⊗[K] L) →ₐ[K]
        (Kfull ⊗[K] L) :=
    Algebra.TensorProduct.map (eFull.restrictScalars K) (AlgHom.id K L)
  have htensorMap : Function.Bijective tensorMap :=
    Algebra.TensorProduct.map_bijective eFull.bijective
      Function.bijective_id
  let tensorEquiv :
      (GenericTensorFieldComponent mFull ⊗[K] L) ≃ₐ[K]
        (Kfull ⊗[K] L) :=
    AlgEquiv.ofBijective tensorMap htensorMap
  let finalMap :
      (GenericTensorFieldComponent mFull ⊗[K] L) →ₐ[K]
        GenericTensorFieldComponent m :=
    (Ideal.Quotient.mkₐ K m).comp tensorEquiv.toAlgHom
  have hfinalMap : Function.Surjective finalMap :=
    Ideal.Quotient.mk_surjective.comp tensorEquiv.surjective
  let m' : Ideal
      (GenericTensorFieldComponent mFull ⊗[K] L) :=
    RingHom.ker finalMap.toRingHom
  let : m'.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective finalMap.toRingHom hfinalMap
  let finalEquiv : GenericTensorFieldComponent m' ≃ₐ[K]
      GenericTensorFieldComponent m :=
    Ideal.quotientKerAlgEquivOfSurjective hfinalMap
  let : FiniteDimensional K Kfull :=
    finiteDimensional_targetField_produced base fullTarget
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := Froot)
    (F' := GenericTensorFieldComponent mFull) (L := L) m'
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := Froot)
      (F' := GenericTensorFieldComponent mFull) (L := L) m'
  let : Algebra L (GenericTensorFieldComponent n) :=
    genericTensorFieldComponentRightAlgebra n
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  obtain ⟨unit, hdecomp⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base target hvarpi hpi
  let rootL : GenericTensorFieldComponent n :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := e) varpi n
  let jL : GenericTensorFieldComponent n →ₐ[L]
      AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      he varpi hvarpiPrime n
  let betaL : AlgebraicClosure L := jL rootL
  have hbetaL : betaL ^ e =
      algebraMap K (AlgebraicClosure L) (varpi : K) :=
    fixedTensorComponentEmbeddedRoot_pow
      base he varpi hvarpiPrime n
  obtain ⟨factorL⟩ :=
    higherRadicalUnitFactorData
      base target varpi hvarpi pi unit hpi hdecomp
      e (dvd_refl e) betaL hbetaL
  have hcomponent : Function.Bijective
      (genericTensorFieldComponentRight m') :=
    lowerUnitFactorExactRootFullTower_finalComponent_rightAlgebraMap_bijective
      (K := K) (Froot := Froot)
      (Omega := Kfull) (L := L)
      base fullTarget target varpi hvarpi hdiv
      piFull pi mFull factorFull m' factorL
  have hmk (z : GenericTensorFieldComponent mFull ⊗[K] L) :
      finalEquiv (Ideal.Quotient.mk m' z) = finalMap z := by
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hfinalMap z
  have hcoord (z : L) :
      finalEquiv (genericTensorFieldComponentRight m' z) =
        genericTensorFieldComponentRight m z := by
    change finalEquiv (Ideal.Quotient.mk m'
        ((1 : GenericTensorFieldComponent mFull) ⊗ₜ[K] z)) =
      Ideal.Quotient.mk m ((1 : Kfull) ⊗ₜ[K] z)
    rw [hmk]
    change Ideal.Quotient.mk m
      (tensorMap
        ((1 : GenericTensorFieldComponent mFull) ⊗ₜ[K] z)) = _
    simp [tensorMap, Algebra.TensorProduct.map_tmul]
  have htransported : Function.Bijective
      (fun z : L ↦ finalEquiv
        (genericTensorFieldComponentRight m' z)) := by
    change Function.Bijective
      (finalEquiv ∘ genericTensorFieldComponentRight m')
    exact finalEquiv.bijective.comp hcomponent
  change Function.Bijective (genericTensorFieldComponentRight m)
  simpa only [hcoord] using htransported

end EtaleFundamentalGroups.Kummer

end

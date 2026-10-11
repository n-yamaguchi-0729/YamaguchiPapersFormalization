/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
import Nyll.EtaleFundamentalGroups.GenericTensor.ActualCompositumComponent
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor

/-!
# The lower unit factor inside the higher actual component

DVR unit absorption selects a literal integral factor `Cq` over the
ramification-index root ring `Rₑ`.  A prescribed larger root determines a
specific extension `K'` of the lower radical field.  This file records the
maximal generic component of `K' ⊗[Rₑ] Cq` whose quotient is the actual
higher compositum.  The construction consumes the sourced
`HigherRadicalUnitFactorData`; it does not choose a second unit factor.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

private theorem finiteDimensional_targetField
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
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

private theorem finiteDimensional_lowerCompositum
    {K : Type u} {L Omega : Type v}
    [Field K] [Field L] [Field Omega]
    [Algebra K L] [Algebra L Omega] [Algebra K Omega]
    [IsScalarTower K L Omega] [FiniteDimensional K L]
    (e N : ℕ) (beta : Omega) :
    let F := lowerRadicalField (K := K) e N beta
    let E := targetCompositumOverLowerRadical
      (K := K) (L := L) e N beta
    FiniteDimensional F E := by
  let F := lowerRadicalField (K := K) e N beta
  let Limage : IntermediateField K Omega :=
    (IsScalarTower.toAlgHom K L Omega).fieldRange
  let E := targetCompositumOverLowerRadical
    (K := K) (L := L) e N beta
  let : FiniteDimensional K Limage :=
    Module.Finite.equiv
      (IsScalarTower.toAlgHom K L Omega).equivFieldRange.toLinearEquiv
  let eSupE : (Limage ⊔ F : IntermediateField K Omega) ≃ₐ[F] E :=
    { toFun := fun z ↦ ⟨z.1, z.2⟩
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  let : FiniteDimensional F
      (Limage ⊔ F : IntermediateField K Omega) :=
    DiscreteValuationField.FieldCompositum.finiteDimensional_sup_over_right_of_left
      Limage F
  exact Module.Finite.equiv eSupE.toLinearEquiv

/-- The maximal ideal selecting the actual higher compositum from the same
lower unit factor used by the DVR absorption construction. -/
noncomputable def lowerUnitFactorHigherGenericComponentIdeal
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let F : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let K' : IntermediateField F (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    letI : IsFractionRing V K := base.valuationSubring_isFractionRing
    letI : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
    letI : Algebra V F :=
      ((algebraMap K F).comp (algebraMap V K)).toAlgebra
    letI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    letI : Algebra Rₑ F :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    letI : Algebra Rₑ K' :=
      ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
    letI : IsScalarTower Rₑ F K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    Ideal (K' ⊗[Rₑ] Cq) := by
  dsimp only
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Cq := AdjoinRoot factor.q
  let F : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let E : IntermediateField F (AlgebraicClosure L) :=
    targetCompositumOverLowerRadical (K := K) (L := L) e N beta
  let K' : IntermediateField F (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  letI : IsFractionRing V K := base.valuationSubring_isFractionRing
  letI : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
  letI : Algebra V F :=
    ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  letI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
  let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
    pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
  letI : Algebra Rₑ F :=
    (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
  letI : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  letI : Algebra Rₑ K' :=
    ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
  letI : IsScalarTower Rₑ F K' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eGeneric : (F ⊗[Rₑ] Cq) ≃ₐ[F] E :=
    lowerUnitFactorGenericFiberAlgEquiv
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  exact actualCompositumGenericComponentIdeal E K' eGeneric

/-- The selected component ideal is the kernel of the native actual-compositum
map built from the same prescribed lower factor and its generic coordinate. -/
private theorem lowerUnitFactorHigherGenericComponentIdeal_eq_actualCompositum
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let F : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let E : IntermediateField F (AlgebraicClosure L) :=
      targetCompositumOverLowerRadical (K := K) (L := L) e N beta
    let K' : IntermediateField F (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
    let : Algebra V F :=
      ((algebraMap K F).comp (algebraMap V K)).toAlgebra
    let : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    let : Algebra Rₑ F :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let : Algebra Rₑ K' :=
      ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
    let : IsScalarTower Rₑ F K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    let eGeneric : (F ⊗[Rₑ] Cq) ≃ₐ[F] E :=
      lowerUnitFactorGenericFiberAlgEquiv
        base target varpi pi N beta he hvarpiPrime halphaPow factor
    lowerUnitFactorHigherGenericComponentIdeal
        base target varpi pi N beta he hvarpiPrime halphaPow factor =
      actualCompositumGenericComponentIdeal E K' eGeneric := by
  intro V e alpha Rₑ Cq F E K' hFrac hClosed algVF towerVKF eRₑ
    algReF algReCq algReKprime towerReFKprime eGeneric
  rfl

/-- The lower-factor component ideal is maximal. -/
theorem lowerUnitFactorHigherGenericComponentIdeal_isMaximal
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let F : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let K' : IntermediateField F (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    letI : IsFractionRing V K := base.valuationSubring_isFractionRing
    letI : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
    letI : Algebra V F :=
      ((algebraMap K F).comp (algebraMap V K)).toAlgebra
    letI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    letI : Algebra Rₑ F :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    letI : Algebra Rₑ K' :=
      ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
    letI : IsScalarTower Rₑ F K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    (lowerUnitFactorHigherGenericComponentIdeal
      base target varpi pi N beta he hvarpiPrime halphaPow factor).IsMaximal := by
  dsimp only
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Cq := AdjoinRoot factor.q
  let F : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let E : IntermediateField F (AlgebraicClosure L) :=
    targetCompositumOverLowerRadical (K := K) (L := L) e N beta
  let K' : IntermediateField F (AlgebraicClosure L) :=
    higherRadicalFieldOverLower (K := K) e N beta
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
  let : Algebra V F :=
    ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
  let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
    pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
  let : Algebra Rₑ F :=
    (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let : Algebra Rₑ K' :=
    ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
  let : IsScalarTower Rₑ F K' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K L := finiteDimensional_targetField base target
  let : FiniteDimensional F E := finiteDimensional_lowerCompositum e N beta
  let eGeneric : (F ⊗[Rₑ] Cq) ≃ₐ[F] E :=
    lowerUnitFactorGenericFiberAlgEquiv
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  change (actualCompositumGenericComponentIdeal E K' eGeneric).IsMaximal
  exact actualCompositumGenericComponentIdeal_isMaximal E K' eGeneric

/-- The quotient selected from the higher generic fibre is canonically the
actual higher compositum. -/
noncomputable def lowerUnitFactorHigherGenericComponentAlgEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let F : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let E : IntermediateField F (AlgebraicClosure L) :=
      targetCompositumOverLowerRadical (K := K) (L := L) e N beta
    let K' : IntermediateField F (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    let M : IntermediateField F (AlgebraicClosure L) := E ⊔ K'
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
    let : Algebra V F :=
      ((algebraMap K F).comp (algebraMap V K)).toAlgebra
    let : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    let : Algebra Rₑ F :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let : Algebra Rₑ K' :=
      ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
    let : IsScalarTower Rₑ F K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    ((K' ⊗[Rₑ] Cq) ⧸
      lowerUnitFactorHigherGenericComponentIdeal
        base target varpi pi N beta he hvarpiPrime halphaPow factor) ≃ₐ[K'] M := by
  intro V e alpha Rₑ Cq F E K' M hFrac hClosed algVF towerVKF eRₑ
    algReF algReCq algReKprime towerReFKprime
  let : FiniteDimensional K L := finiteDimensional_targetField base target
  let : FiniteDimensional F E := finiteDimensional_lowerCompositum e N beta
  let eGeneric : (F ⊗[Rₑ] Cq) ≃ₐ[F] E :=
    lowerUnitFactorGenericFiberAlgEquiv
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  exact (Ideal.quotientEquivAlgOfEq K'
    (lowerUnitFactorHigherGenericComponentIdeal_eq_actualCompositum
      base target varpi pi N beta he hvarpiPrime halphaPow factor)).trans
        (actualCompositumGenericComponentAlgEquiv E K' eGeneric)

/-- The generic lower-factor comparison sends its distinguished integral
root to the unit-absorption root in the common algebraic closure. -/
theorem lowerUnitFactorGenericFiberAlgEquiv_root_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let F : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let E : IntermediateField F (AlgebraicClosure L) :=
      targetCompositumOverLowerRadical (K := K) (L := L) e N beta
    letI : IsFractionRing V K := base.valuationSubring_isFractionRing
    letI : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
    letI : Algebra V F :=
      ((algebraMap K F).comp (algebraMap V K)).toAlgebra
    letI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    letI : Algebra Rₑ F :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    (((lowerUnitFactorGenericFiberAlgEquiv
        base target varpi pi N beta he hvarpiPrime halphaPow factor)
      (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q) : E) :
        AlgebraicClosure L) = factor.delta := by
  dsimp only
  let V := base.valuationSubring
  let W := target.valuationSubring
  let e := ramificationIndex base target
  let alpha : AlgebraicClosure L := beta ^ (N / e)
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Cq := AdjoinRoot factor.q
  let F : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
  let E₀ : IntermediateField L (AlgebraicClosure L) :=
    IntermediateField.adjoin L
      ({factor.delta} : Set (AlgebraicClosure L))
  let E : IntermediateField F (AlgebraicClosure L) :=
    targetCompositumOverLowerRadical (K := K) (L := L) e N beta
  let Limage : IntermediateField K (AlgebraicClosure L) :=
    (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).fieldRange
  let lToE : L →ₐ[K] E :=
    { toFun := fun z ↦ ⟨algebraMap L (AlgebraicClosure L) z, by
          change algebraMap L (AlgebraicClosure L) z ∈ Limage ⊔ F
          exact SetLike.coe_mono
            (show Limage ≤ Limage ⊔ F from le_sup_left)
            (AlgHom.mem_fieldRange.mpr ⟨z, rfl⟩)⟩
      map_one' := by apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; simp
      map_add' _ _ := by apply Subtype.ext; simp
      map_mul' _ _ := by apply Subtype.ext; simp
      commutes' := fun z ↦ by
        apply Subtype.ext
        exact IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) z }
  let : Algebra L E := lToE.toRingHom.toAlgebra
  let : IsScalarTower K L E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hCompositum' : E₀.restrictScalars K = Limage ⊔ F := by
    simpa [E₀, Limage, F, alpha, e] using factor.compositum_eq
  let eE : E₀ ≃ₐ[L] E :=
    { toFun := fun z ↦ ⟨z.1, by
          change z.1 ∈ Limage ⊔ F
          rw [← hCompositum']
          exact z.2⟩
      invFun := fun z ↦ ⟨z.1, by
          have hz : z.1 ∈ Limage ⊔ F := z.2
          rw [← hCompositum'] at hz
          exact hz⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl
      commutes' := fun _ ↦ rfl }
  have hqIrreducibleMap :
      Irreducible (factor.q.map (algebraMap W L)) := by
    rw [factor.q_map]
    exact minpoly.irreducible
      (Algebra.IsIntegral.isIntegral factor.delta)
  have hqIrreducible : Irreducible factor.q :=
    (factor.q_monic.irreducible_iff_irreducible_map_fraction_map).2
      hqIrreducibleMap
  let : IsDomain Cq := AdjoinRoot.isDomain_of_prime hqIrreducible.prime
  let eCq : (L ⊗[W] Cq) ≃ₐ[L] E :=
    (adjoinRootGenericFactorAlgEquiv factor.q
      factor.unitFactorEquiv).trans eE
  let : Algebra Cq E :=
    (genericFiberRightAlgHom eCq).toRingHom.toAlgebra
  let : IsFractionRing Cq E :=
    isFractionRing_of_genericFiberAlgEquiv eCq
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
  let : Algebra V F :=
    ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
  let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
    pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
  let : IsDomain Rₑ :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime he varpi hvarpiPrime
  let : Algebra Rₑ F :=
    (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
  let : IsFractionRing Rₑ F :=
    isFractionRing_of_genericFiberAlgEquiv eRₑ
  let radicalMap : Rₑ →ₐ[V] Cq := factor.radicalToUnitFactor
  let : Algebra Rₑ Cq := radicalMap.toRingHom.toAlgebra
  let : Algebra Rₑ E :=
    ((algebraMap F E).comp (algebraMap Rₑ F)).toAlgebra
  let : IsScalarTower Rₑ F E := IsScalarTower.of_algebraMap_eq' rfl
  have hCqRoot :
      (((genericFiberRightAlgHom eCq) (AdjoinRoot.root factor.q) : E) :
        AlgebraicClosure L) = factor.delta := by
    change ((eE ((adjoinRootGenericFactorAlgEquiv factor.q
        factor.unitFactorEquiv)
        (1 ⊗ₜ[W] AdjoinRoot.root factor.q)) : E) :
      AlgebraicClosure L) = factor.delta
    rw [adjoinRootGenericFactorAlgEquiv_tmul_root,
      factor.unitFactor_root]
    rfl
  have hCqCoeff :
      (((genericFiberRightAlgHom eCq)
          (algebraMap W Cq pi) : E) : AlgebraicClosure L) =
        algebraMap L (AlgebraicClosure L) (pi : L) := by
    rw [(genericFiberRightAlgHom eCq).commutes]
    rfl
  have hRₑRoot :
      (((genericFiberRightAlgHom eRₑ)
          (AdjoinRoot.root (X ^ e - C varpi)) : F) :
        AlgebraicClosure L) = alpha := by
    change (((pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha
        halphaPow) (1 ⊗ₜ[V] AdjoinRoot.root (X ^ e - C varpi)) :
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))) :
        AlgebraicClosure L) = alpha
    exact congrArg Subtype.val
      (pureRadicalGenericFiberAlgEquiv_tmul_root
        he varpi hvarpiPrime alpha halphaPow)
  have hCqBase (z : V) :
      (((genericFiberRightAlgHom eCq)
          (radicalMap (algebraMap V Rₑ z)) : E) :
        AlgebraicClosure L) =
      algebraMap K (AlgebraicClosure L) (z : K) := by
    rw [radicalMap.commutes]
    change (((genericFiberRightAlgHom eCq)
        (algebraMap W Cq (integerMap base target z)) : E) :
      AlgebraicClosure L) =
        algebraMap K (AlgebraicClosure L) (z : K)
    rw [(genericFiberRightAlgHom eCq).commutes]
    rfl
  have hRₑBase (z : V) :
      ((algebraMap F E ((genericFiberRightAlgHom eRₑ)
          (algebraMap V Rₑ z)) : E) : AlgebraicClosure L) =
        algebraMap K (AlgebraicClosure L) (z : K) := by
    rw [(genericFiberRightAlgHom eRₑ).commutes]
    rfl
  have hTowerRₑCqE :
      (genericFiberRightAlgHom eCq).toRingHom.comp radicalMap.toRingHom =
        (algebraMap F E).comp (genericFiberRightAlgHom eRₑ).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro z
      apply E.toSubfield.subtype.injective
      change (((genericFiberRightAlgHom eCq)
          (radicalMap (algebraMap V Rₑ z)) : E) :
            AlgebraicClosure L) =
        ((algebraMap F E ((genericFiberRightAlgHom eRₑ)
          (algebraMap V Rₑ z)) : E) : AlgebraicClosure L)
      exact hCqBase z |>.trans (hRₑBase z).symm
    · apply E.toSubfield.subtype.injective
      change (((genericFiberRightAlgHom eCq)
          (radicalMap (AdjoinRoot.root (X ^ e - C varpi))) : E) :
            AlgebraicClosure L) =
        ((algebraMap F E ((genericFiberRightAlgHom eRₑ)
          (AdjoinRoot.root (X ^ e - C varpi))) : E) :
            AlgebraicClosure L)
      rw [show radicalMap (AdjoinRoot.root (X ^ e - C varpi)) =
          AdjoinRoot.root factor.q * algebraMap W Cq pi from
        factor.radical_root]
      simp only [map_mul]
      change (((genericFiberRightAlgHom eCq)
          (AdjoinRoot.root factor.q) : E) : AlgebraicClosure L) *
          (((genericFiberRightAlgHom eCq)
            (algebraMap W Cq pi) : E) : AlgebraicClosure L) =
        ((algebraMap F E ((genericFiberRightAlgHom eRₑ)
          (AdjoinRoot.root (X ^ e - C varpi))) : E) :
            AlgebraicClosure L)
      rw [hCqRoot, hCqCoeff]
      change factor.delta *
          algebraMap L (AlgebraicClosure L) (pi : L) =
        (((genericFiberRightAlgHom eRₑ)
          (AdjoinRoot.root (X ^ e - C varpi)) : F) :
            AlgebraicClosure L)
      rw [hRₑRoot]
      exact factor.alpha_eq.symm
  let : IsScalarTower Rₑ Cq E :=
    IsScalarTower.of_algebraMap_eq fun z ↦
      DFunLike.congr_fun hTowerRₑCqE z |>.symm
  let : Module.Finite V Rₑ :=
    (monic_X_pow_sub_C varpi he.ne').finite_adjoinRoot
  let : Module.Finite W Cq := factor.q_finite
  let : Module.Finite V Cq := Module.Finite.trans W Cq
  let : IsScalarTower V Rₑ Cq :=
    IsScalarTower.of_algebraMap_eq fun z ↦
      (radicalMap.commutes z).symm
  let : Module.Finite Rₑ Cq :=
    Module.Finite.of_restrictScalars_finite V Rₑ Cq
  change (((finiteGenericFiberAlgEquiv
      (R := Rₑ) (C := Cq) (K := F) (E := E))
      (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q) : E) :
        AlgebraicClosure L) = factor.delta
  rw [finiteGenericFiberAlgEquiv_tmul]
  simp only [map_one, one_mul]
  exact hCqRoot

/-- Compute a tensor coordinate after the quotient identification in the
small generic context, before specializing its rings to the radical tower. -/
private theorem quotientComparison_tmul_right_coe
    {A : Type u} {T : Type v} {F : Type w} {Omega : Type x}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F] [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K'] [FiniteDimensional F E]
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) (I : Ideal (K' ⊗[A] T))
    (hI : I = actualCompositumGenericComponentIdeal E K' eGeneric) (c : T) :
    ((((Ideal.quotientEquivAlgOfEq K' hI).trans
          (actualCompositumGenericComponentAlgEquiv E K' eGeneric))
        (Ideal.Quotient.mk I (1 ⊗ₜ[A] c)) :
          (E ⊔ K' : IntermediateField F Omega)) : Omega) =
      ((eGeneric (1 ⊗ₜ[A] c) : E) : Omega) := by
  rw [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    actualCompositumGenericComponentAlgEquiv_mk,
    actualCompositumGenericComponentMap_tmul_right_coe]

/-- The quotient equivalence retains the distinguished root coordinate of
the exact lower unit factor used by the absorption construction. -/
theorem lowerUnitFactorHigherGenericComponentAlgEquiv_root_coe
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (he : 0 < ramificationIndex base target)
    (hvarpiPrime : Prime varpi)
    (halphaPow :
      (beta ^ (N / ramificationIndex base target)) ^
          ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K))
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    let V := base.valuationSubring
    let e := ramificationIndex base target
    let alpha : AlgebraicClosure L := beta ^ (N / e)
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    let F : IntermediateField K (AlgebraicClosure L) :=
      IntermediateField.adjoin K ({alpha} : Set (AlgebraicClosure L))
    let E : IntermediateField F (AlgebraicClosure L) :=
      targetCompositumOverLowerRadical (K := K) (L := L) e N beta
    let K' : IntermediateField F (AlgebraicClosure L) :=
      higherRadicalFieldOverLower (K := K) e N beta
    let M : IntermediateField F (AlgebraicClosure L) := E ⊔ K'
    let : IsFractionRing V K := base.valuationSubring_isFractionRing
    let : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
    let : Algebra V F :=
      ((algebraMap K F).comp (algebraMap V K)).toAlgebra
    let : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq' rfl
    let eRₑ : (K ⊗[V] Rₑ) ≃ₐ[K] F :=
      pureRadicalGenericFiberAlgEquiv he varpi hvarpiPrime alpha halphaPow
    let : Algebra Rₑ F :=
      (genericFiberRightAlgHom eRₑ).toRingHom.toAlgebra
    let : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let : Algebra Rₑ K' :=
      ((algebraMap F K').comp (algebraMap Rₑ F)).toAlgebra
    let : IsScalarTower Rₑ F K' :=
      IsScalarTower.of_algebraMap_eq' rfl
    let I := lowerUnitFactorHigherGenericComponentIdeal
      base target varpi pi N beta he hvarpiPrime halphaPow factor
    (((lowerUnitFactorHigherGenericComponentAlgEquiv
        base target varpi pi N beta he hvarpiPrime halphaPow factor)
      (Ideal.Quotient.mk I
        (1 ⊗ₜ[Rₑ] AdjoinRoot.root factor.q)) : M) :
          AlgebraicClosure L) = factor.delta := by
  intro V e alpha Rₑ Cq F E K' M hFrac hClosed algVF towerVKF eRₑ
    algReF algReCq algReKprime towerReFKprime I
  let : Algebra K' M :=
    DiscreteValuationField.FieldCompositum.supRightAlgebra
      (K := F) (Ω := AlgebraicClosure L) E K'
  let : FiniteDimensional K L := finiteDimensional_targetField base target
  let : FiniteDimensional F E := finiteDimensional_lowerCompositum e N beta
  let eGeneric : (F ⊗[Rₑ] Cq) ≃ₐ[F] E :=
    lowerUnitFactorGenericFiberAlgEquiv
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  have hIdeal : I = actualCompositumGenericComponentIdeal E K' eGeneric :=
    lowerUnitFactorHigherGenericComponentIdeal_eq_actualCompositum
      base target varpi pi N beta he hvarpiPrime halphaPow factor
  have hResult :=
    (quotientComparison_tmul_right_coe E K' eGeneric I hIdeal
      (AdjoinRoot.root factor.q)).trans
        (lowerUnitFactorGenericFiberAlgEquiv_root_coe
          base target varpi pi N beta he hvarpiPrime halphaPow factor)
  dsimp only [lowerUnitFactorHigherGenericComponentAlgEquiv]
  exact hResult

end EtaleFundamentalGroups.Kummer

end

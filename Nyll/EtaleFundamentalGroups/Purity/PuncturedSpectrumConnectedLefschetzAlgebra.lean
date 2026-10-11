/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedLefschetzSource
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.Support

/-!
# Algebraic inputs for connected hypersurface restrictions

This file records the completeness and codimension properties of the finite
integral-closure model attached to a connected finite-etale cover of a
punctured local spectrum.  These are the algebraic inputs preceding the
connectedness theorem for a punctured hypersurface.

No connectedness conclusion is assumed here.
-/

noncomputable section

open CategoryTheory IsLocalRing
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v

/-- A finite algebra over a complete Noetherian local ring is complete for
the extension of every ideal contained in the maximal ideal. -/
theorem isAdicComplete_map_of_moduleFinite_of_le_maximalIdeal
    {R : Type u} {C : Type v} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [Module.Finite R C]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    IsAdicComplete (I.map (algebraMap R C)) C := by
  let : IsAdicComplete I R :=
    EtaleFundamentalGroups.Purity.isAdicComplete_of_le_maximalIdeal
      (M := R) I hI
  have hcomplete : IsAdicComplete I C :=
    ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite
      (I := I) (M := C)
  exact (IsAdicComplete.map_algebraMap_iff (I := I) (M := C) (S := C)).2
    hcomplete

/-- The integral closure in a field extension of a fraction field is a
faithful algebra over the base domain. -/
theorem integralClosure_faithfulSMul_of_fractionField
    {R K L : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] :
    FaithfulSMul R (integralClosure R L) := by
  apply (faithfulSMul_iff_algebraMap_injective
    R (integralClosure R L)).mpr
  intro x z hxz
  apply IsFractionRing.injective R K
  apply (algebraMap K L).injective
  have hxL := congrArg (fun c : integralClosure R L ↦ (c : L)) hxz
  change algebraMap R L x = algebraMap R L z at hxL
  calc
    algebraMap K L (algebraMap R K x) = algebraMap R L x :=
      (IsScalarTower.algebraMap_apply R K L x).symm
    _ = algebraMap R L z := hxL
    _ = algebraMap K L (algebraMap R K z) :=
      IsScalarTower.algebraMap_apply R K L z

/-- In a faithfully integral domain extension of an integrally closed local
domain, a prime above the maximal ideal has the same height as the maximal
ideal. -/
theorem prime_height_eq_ringKrullDim_of_map_maximalIdeal_le
    {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] [CommRing C] [IsDomain C]
    [Algebra R C] [Algebra.IsIntegral R C] [FaithfulSMul R C]
    (P : Ideal C) [P.IsPrime]
    (hP : (maximalIdeal R).map (algebraMap R C) ≤ P) :
    ((P.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim R := by
  have hm_le : maximalIdeal R ≤ P.under R := by
    rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap]
    exact hP
  have hund_ne : P.under R ≠ ⊤ :=
    (inferInstance : (P.under R).IsPrime).ne_top
  have hund_le : P.under R ≤ maximalIdeal R := le_maximalIdeal hund_ne
  have hund : P.under R = maximalIdeal R := le_antisymm hund_le hm_le
  have hheight : P.height = (P.under R).height :=
    (open _root_.EtaleFundamentalGroups.SpecialLocalPurity in
      height_eq_height_under_of_faithfully_integral_over_integrallyClosed
        (R := R) (S := C) P)
  rw [hheight, hund, IsLocalRing.maximalIdeal_height_eq_ringKrullDim]

/-- Codimension-three form of
`prime_height_eq_ringKrullDim_of_map_maximalIdeal_le`. -/
theorem three_le_prime_height_of_map_maximalIdeal_le
    {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] [CommRing C] [IsDomain C]
    [Algebra R C] [Algebra.IsIntegral R C] [FaithfulSMul R C]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R)
    (P : Ideal C) [P.IsPrime]
    (hP : (maximalIdeal R).map (algebraMap R C) ≤ P) :
    ((3 : ℕ∞) : WithBot ℕ∞) ≤ ((P.height : ℕ∞) : WithBot ℕ∞) := by
  rw [prime_height_eq_ringKrullDim_of_map_maximalIdeal_le P hP]
  exact hdim

/-- The integral-closure model of a connected punctured cover is complete
along the extension of every ideal contained in the maximal ideal. -/
theorem connectedPuncturedCover_integralClosure_isAdicComplete
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsAdicComplete
      (I.map (algebraMap R (integralClosure R W.left.functionField)))
      (integralClosure R W.left.functionField) := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let K : Type u := U.functionField
  let : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure R L
  let : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  exact isAdicComplete_map_of_moduleFinite_of_le_maximalIdeal I hI

/-- Every prime of the connected-cover integral closure above the closed
point has codimension at least three when the base has dimension at least
three. -/
theorem connectedPuncturedCover_integralClosure_three_le_prime_height
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R
        (show (1 : WithBot ℕ∞) ≤ ringKrullDim R from le_trans (by norm_num) hdim)
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R
        (show (1 : WithBot ℕ∞) ≤ ringKrullDim R from le_trans (by norm_num) hdim)
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R
        (show (1 : WithBot ℕ∞) ≤ ringKrullDim R from le_trans (by norm_num) hdim)
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ (P : Ideal (integralClosure R W.left.functionField))
      [P.IsPrime],
      (maximalIdeal R).map
          (algebraMap R (integralClosure R W.left.functionField)) ≤ P →
        ((3 : ℕ∞) : WithBot ℕ∞) ≤
          ((P.height : ℕ∞) : WithBot ℕ∞) := by
  dsimp only
  have hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by norm_num) hdim
  let U := Scheme.puncturedSpectrum R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let K : Type u := U.functionField
  let : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure R L
  let : FaithfulSMul R C :=
    integralClosure_faithfulSMul_of_fractionField (R := R) (K := K) (L := L)
  let : Algebra.IsIntegral R C := integralClosure.AlgebraIsIntegral
  intro P _ hP
  exact three_le_prime_height_of_map_maximalIdeal_le hdim P hP

end AlgebraicGeometry.FiniteEtale

end

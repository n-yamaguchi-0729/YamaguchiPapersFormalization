/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedNormalizationLocal
import EtaleFundamentalGroups.Purity.PuncturedSpectrumConnectedLefschetzAlgebra
import ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower

/-!
# Maximal-adic completeness of connected finite normalizations

A finite local integral algebra over a complete Noetherian local ring is
complete for its own maximal ideal.  This supplies the completeness input
for the finite normalization attached to a connected punctured cover.
-/

noncomputable section

open IsLocalRing
open CategoryTheory.PreGaloisCategory
open ValuationTheory.DiscreteValuationField

namespace AlgebraicGeometry.FiniteEtale

universe u v

/-- A finite local integral algebra over a maximal-adically complete
Noetherian local ring is complete for its own maximal ideal. -/
theorem isAdicComplete_maximalIdeal_of_moduleFinite_of_integral_local
    {R : Type u} {C : Type v}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing C] [IsLocalRing C] [Algebra R C]
    [Module.Finite R C] [Algebra.IsIntegral R C] :
    IsAdicComplete (maximalIdeal C) C := by
  let I : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let J : Ideal C := maximalIdeal C
  have hcompleteBase : IsAdicComplete (maximalIdeal R) C :=
    ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite
      (I := maximalIdeal R) (M := C)
  let : IsAdicComplete I C :=
    (IsAdicComplete.map_algebraMap_iff
      (I := maximalIdeal R) (M := C) (S := C)).2 hcompleteBase
  let : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  have hIJ : I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    have hmax : ((maximalIdeal C).comap
        (algebraMap R C)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R C)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) (maximalIdeal C)
    rw [(IsLocalRing.maximal_ideal_unique R).unique hmax
      (maximalIdeal.isMaximal R)]
  have hJradical : J ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP ↦ ?_
    rcases hP with ⟨hIP, hPprime⟩
    let : P.IsPrime := hPprime
    have hbase_le : maximalIdeal R ≤ P.comap (algebraMap R C) :=
      (Ideal.map_le_iff_le_comap).1 hIP
    have hcomap_ne_top : P.comap (algebraMap R C) ≠ ⊤ :=
      (show (P.comap (algebraMap R C)).IsPrime from inferInstance).ne_top
    have hcomap_maximal : (P.comap (algebraMap R C)).IsMaximal := by
      rw [← (maximalIdeal.isMaximal R).eq_of_le hcomap_ne_top hbase_le]
      exact maximalIdeal.isMaximal R
    have hPmaximal : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        (algebraMap R C) (fun x ↦ Algebra.IsIntegral.isIntegral x)
        P hcomap_maximal
    have hP : P = J := by
      simpa only [J] using IsLocalRing.eq_maximalIdeal hPmaximal
    rw [hP]
  obtain ⟨n, hn⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hJradical
      J.fg_of_isNoetherianRing
  have hn' : J ^ (n + 1) ≤ I :=
    (Ideal.pow_le_pow_right (Nat.le_add_right n 1)).trans hn
  exact isAdicComplete_of_le_of_pow_le
    I J (Nat.zero_lt_succ n) hIJ
      (by simpa only [Nat.succ_eq_add_one] using hn')

/-- The integral-closure algebra attached to a connected punctured cover of
a positive-dimensional complete normal local spectrum is complete for its
own maximal ideal. -/
theorem connectedPuncturedCover_integralClosure_isAdicComplete_maximalIdeal
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
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
    letI : Module.Finite R (integralClosure R W.left.functionField) :=
      connectedPuncturedCover_integralClosure_finite_of_positiveDimension
        R hpos W
    letI : IsLocalRing (integralClosure R W.left.functionField) :=
      connectedPuncturedCover_integralClosure_isLocalRing
        (R := R) hpos W
    IsAdicComplete
      (maximalIdeal (integralClosure R W.left.functionField))
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
  let : IsLocalRing C :=
    connectedPuncturedCover_integralClosure_isLocalRing (R := R) hpos W
  exact
    isAdicComplete_maximalIdeal_of_moduleFinite_of_integral_local
      (R := R) (C := C)

end AlgebraicGeometry.FiniteEtale

end

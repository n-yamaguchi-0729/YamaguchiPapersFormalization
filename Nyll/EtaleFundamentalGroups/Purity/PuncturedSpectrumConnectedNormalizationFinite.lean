/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.StalkFunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumFunctionField

/-!
# Finite connected normalizations across a punctured spectrum

For a connected finite-etale cover of the puncture of a
positive-dimensional normal Noetherian local domain, the integral closure in
the cover's function field is finite over the local domain.  No finite-type
hypothesis over `ℤ`, and no dimension-two hypothesis, is used.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]

/-- For a connected finite-etale cover of a positive-dimensional punctured
local spectrum, the integral closure of a normal Noetherian local domain in
the cover's function field is finite. -/
theorem connectedPuncturedCover_integralClosure_finite_of_positiveDimension
    [IsNoetherianRing R] [IsIntegrallyClosed R]
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
    letI : FiniteDimensional U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : Algebra.IsSeparable U.functionField W.left.functionField :=
      EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
    Module.Finite R (integralClosure R W.left.functionField) := by
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
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  exact IsIntegralClosure.finite R K L (integralClosure R L)

/-- The integral-closure normalization of a connected finite-etale cover of
the puncture, as an actual scheme over the full local spectrum. -/
noncomputable def
    connectedPuncturedCoverIntegralClosureOverOfPositiveDimension
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    Over (Spec (.of R)) := by
  let U := Scheme.puncturedSpectrum R
  letI : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  letI : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let K : Type u := U.functionField
  letI : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  letI : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  letI : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  letI : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let C := integralClosure R L
  exact Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C)))

/-- The connected punctured-cover normalization is finite over the full
local spectrum in every positive dimension. -/
theorem connectedPuncturedCoverIntegralClosureOver_hom_isFinite
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    IsFinite
      (connectedPuncturedCoverIntegralClosureOverOfPositiveDimension
        R hpos W).hom := by
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
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable K L :=
    EtaleFundamentalGroups.isSeparable_functionField_of_finiteEtale_isConnected W
  let C := integralClosure R L
  have hfinite : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  unfold connectedPuncturedCoverIntegralClosureOverOfPositiveDimension
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R C)))
  rw [IsFinite.SpecMap_iff]
  exact hfinite

end AlgebraicGeometry.FiniteEtale

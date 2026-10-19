/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction
import Mathlib.RingTheory.Ideal.Pointwise
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Mathlib.RingTheory.Invariant.Galois
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Mathlib.RingTheory.Ideal.Over

/-!
# Normalization-prime subgroups in finite-etale Galois-cover quotients

Decomposition and ideal inertia groups for a normalization prime are
transported from the function-field Galois group to the categorical finite
quotient represented by the cover.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped Pointwise

namespace EtaleFundamentalGroups.Kummer

universe u uA uB

/-- The normalization-prime decomposition group inside the categorical
finite quotient is the usual function-field decomposition group. -/
noncomputable def finiteEtaleGaloisCoverIdealDecompositionMulEquiv
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      MulAction.stabilizer (Aut Y)ᵐᵒᵖ P ≃*
        MulAction.stabilizer Gal(L/K) P := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction
  exact Ideal.stabilizerEquiv P
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY)
    (finiteEtaleGaloisCoverNormalizationAction_smul Y hY A B)

/-- The normalization-prime inertia subgroup in the categorical finite
quotient is the usual ideal inertia subgroup of the function-field Galois
group. -/
noncomputable def finiteEtaleGaloisCoverIdealInertiaMulEquiv
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ ≃*
        P.toAddSubgroup.inertia Gal(L/K) := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction
  exact Ideal.inertiaEquiv P
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY)
    (finiteEtaleGaloisCoverNormalizationAction_smul Y hY A B)

/-- The categorical finite-quotient inertia image and normalization ideal
inertia have the same order. -/
theorem natCard_finiteEtaleGaloisCoverIdealInertia_eq
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      Nat.card (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ) =
        Nat.card (P.toAddSubgroup.inertia Gal(L/K)) := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction
  exact Nat.card_congr
    (finiteEtaleGaloisCoverIdealInertiaMulEquiv Y hY A B P).toEquiv

/-- Vanishing of the inertia image in the categorical finite quotient is
equivalent to vanishing of normalization ideal inertia in the function-field
Galois group. -/
theorem finiteEtaleGaloisCoverIdealInertia_eq_bot_iff
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    let _ : IsGalois Y := hY
    let _ : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    let _ : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ = ⊥ ↔
        P.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure P hFinite hFieldAction hCoverAction
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  rw [Subgroup.eq_bot_iff_card, Subgroup.eq_bot_iff_card,
    natCard_finiteEtaleGaloisCoverIdealInertia_eq Y hY A B P]

end EtaleFundamentalGroups.Kummer

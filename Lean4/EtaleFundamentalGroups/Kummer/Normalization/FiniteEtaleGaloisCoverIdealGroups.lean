/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction
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
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      MulAction.stabilizer (Aut Y)ᵐᵒᵖ P ≃*
        MulAction.stabilizer Gal(L/K) P := by
  letI : IsGalois Y := hY
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ P
  letI : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
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
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ ≃*
        P.toAddSubgroup.inertia Gal(L/K) := by
  letI : IsGalois Y := hY
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ P
  letI : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  exact Ideal.inertiaEquiv P
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY)
    (finiteEtaleGaloisCoverNormalizationAction_smul Y hY A B)

/-- The categorical finite-quotient inertia image and normalization ideal
inertia have the same order. -/
theorem natCard_finiteEtaleGaloisCoverIdealInertia_eq
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      Nat.card (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ) =
        Nat.card (P.toAddSubgroup.inertia Gal(L/K)) := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ P
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  exact Nat.card_congr
    (finiteEtaleGaloisCoverIdealInertiaMulEquiv Y hY A B P).toEquiv

/-- Vanishing of the inertia image in the categorical finite quotient is
equivalent to vanishing of normalization ideal inertia in the function-field
Galois group. -/
theorem finiteEtaleGaloisCoverIdealInertia_eq_bot_iff
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := X.functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    ∀ (A : Type uA) (B : Type uB)
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegrallyClosed A] [IsIntegralClosure B A L]
      (P : Ideal B),
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ = ⊥ ↔
        P.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K := X.functionField
  let L := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  dsimp only
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ P
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  rw [Subgroup.eq_bot_iff_card, Subgroup.eq_bot_iff_card,
    natCard_finiteEtaleGaloisCoverIdealInertia_eq Y hY A B P]

end EtaleFundamentalGroups.Kummer

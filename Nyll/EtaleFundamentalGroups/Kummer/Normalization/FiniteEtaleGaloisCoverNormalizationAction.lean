/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Mathlib.RingTheory.Invariant.Galois

/-!
# Normalization actions of finite-etale Galois-cover quotients

For a finite-etale Galois cover of a normal integral locally Noetherian
scheme, the opposite categorical automorphism group is the Galois group of
the induced function-field extension.  This file transports the canonical
normalization-ring action across that equivalence.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped Pointwise

namespace EtaleFundamentalGroups.Kummer

universe u uA uB

/-- The action of the categorical Galois-cover quotient on a normalization
ring, transported from the function-field Galois action. -/
@[implicit_reducible]
noncomputable def finiteEtaleGaloisCoverNormalizationAction
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
      [IsIntegrallyClosed A] [IsIntegralClosure B A L],
      MulSemiringAction (Aut Y)ᵐᵒᵖ B := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure
  let hFinite : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let hFieldAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  exact MulSemiringAction.compHom B
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).toMonoidHom

/-- The transported categorical action agrees pointwise with the canonical
function-field Galois action on the normalization. -/
theorem finiteEtaleGaloisCoverNormalizationAction_smul
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
      (sigma : (Aut Y)ᵐᵒᵖ) (b : B),
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      (finiteEtaleAutOpFunctionFieldMulEquiv Y hY sigma) • b = sigma • b := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure sigma b hFinite hFieldAction hCoverAction
  rfl

/-- The categorical cover action on the normalization commutes with the
base-ring scalar action. -/
theorem finiteEtaleGaloisCoverNormalizationSMulCommClass
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
      [IsIntegrallyClosed A] [IsIntegralClosure B A L],
      let _ : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Y
      let _ : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      let _ : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      SMulCommClass (Aut Y)ᵐᵒᵖ A B := by
  intro hCoverGalois hIntegral K L hKL A B hCommA hCommB hAK hFracAK hBL hFracBL hAB hAL hAKL
    hABL hClosed hClosure hFinite hFieldAction hCoverAction
  constructor
  intro sigma a b
  change galRestrict A K L B
      (finiteEtaleAutOpFunctionFieldMulEquiv Y hY sigma) (a • b) =
    a • galRestrict A K L B
      (finiteEtaleAutOpFunctionFieldMulEquiv Y hY sigma) b
  exact map_smul (galRestrict A K L B
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY sigma)) a b

end EtaleFundamentalGroups.Kummer

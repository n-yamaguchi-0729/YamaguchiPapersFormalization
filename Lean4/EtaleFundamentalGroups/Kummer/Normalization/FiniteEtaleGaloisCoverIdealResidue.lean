/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction
import Mathlib.RingTheory.Ideal.Over

/-!
# Residue actions in finite-etale Galois-cover quotients

The residue action of the normalization-prime decomposition group has ideal
inertia as its kernel, both internally and after mapping the kernel into the
full categorical finite quotient.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped Pointwise

namespace EtaleFundamentalGroups.Kummer

universe u uA uB

/-- Reduction on a normalization prime, expressed directly on the
categorical finite quotient of a Galois cover. -/
noncomputable def finiteEtaleGaloisCoverIdealResidueHom
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
      letI : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
        finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
      let p := P.comap (algebraMap A B)
      letI : P.LiesOver p := ⟨rfl⟩
      MulAction.stabilizer (Aut Y)ᵐᵒᵖ P →*
        ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) := by
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
  letI : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
    finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
  let p := P.comap (algebraMap A B)
  letI : P.LiesOver p := ⟨rfl⟩
  exact Ideal.Quotient.stabilizerHom P p (Aut Y)ᵐᵒᵖ

/-- The kernel of the categorical residue action is the ideal inertia inside
the decomposition group. -/
theorem finiteEtaleGaloisCoverIdealResidueHom_ker
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
      letI : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
        finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
      (finiteEtaleGaloisCoverIdealResidueHom Y hY A B P).ker =
        P.toAddSubgroup.inertia
          (MulAction.stabilizer (Aut Y)ᵐᵒᵖ P) := by
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
  let : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
    finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
  let p := P.comap (algebraMap A B)
  let : P.LiesOver p := ⟨rfl⟩
  exact Ideal.Quotient.ker_stabilizerHom P p (Aut Y)ᵐᵒᵖ

/-- Mapping the residue-action kernel back into the finite quotient gives
exactly the normalization-prime ideal inertia image. -/
theorem finiteEtaleGaloisCoverIdealResidueHom_map_ker
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
      letI : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
        finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
      (finiteEtaleGaloisCoverIdealResidueHom Y hY A B P).ker.map
          (Subgroup.subtype (MulAction.stabilizer (Aut Y)ᵐᵒᵖ P)) =
        P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ := by
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
  let : SMulCommClass (Aut Y)ᵐᵒᵖ A B :=
    finiteEtaleGaloisCoverNormalizationSMulCommClass Y hY A B
  let p := P.comap (algebraMap A B)
  let : P.LiesOver p := ⟨rfl⟩
  exact Ideal.Quotient.map_ker_stabilizer_subtype P p (Aut Y)ᵐᵒᵖ

end EtaleFundamentalGroups.Kummer

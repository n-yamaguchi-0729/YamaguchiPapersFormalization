/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealGroups

/-!
# Ideal-inertia images in pointed finite-etale Galois quotients

For the surjective quotient represented by a pointed finite-etale Galois
cover, the inverse image of normalization-prime ideal inertia maps back onto
that exact subgroup.  Combining this quotient statement with the
function-field comparison identifies its order with ordinary ideal inertia.

This is a finite-quotient statement.  It does not construct the separate
strict-henselian local-to-global fundamental-group morphism.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped Pointwise

namespace EtaleFundamentalGroups.Kummer

universe u uA uB

/-- Normalization-prime ideal inertia is exactly the image of its inverse
image under the pointed finite-etale Galois-cover quotient. -/
theorem finiteEtaleGaloisCoverIdealInertia_map_comap
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
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
      Subgroup.map
          (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
          (Subgroup.comap
            (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
            (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)) =
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
  exact finiteEtaleGaloisCoverQuotientMonoidHom_map_comap xi Y hY y
    (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)

/-- The pointed finite-quotient ideal-inertia image has the same order as
the ordinary normalization ideal inertia in the function-field Galois group. -/
theorem natCard_finiteEtaleGaloisCoverIdealInertia_image_eq
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
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
      Nat.card
          (Subgroup.map
            (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
            (Subgroup.comap
              (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
              (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ))) =
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
  rw [finiteEtaleGaloisCoverIdealInertia_map_comap xi Y hY y A B P,
    natCard_finiteEtaleGaloisCoverIdealInertia_eq Y hY A B P]

end EtaleFundamentalGroups.Kummer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms

/-!
# Finite quotients represented by finite-etale Galois covers

A chosen point of the geometric fiber of a finite-etale Galois cover gives
the corresponding surjective finite quotient of the etale fundamental
group.  For a normal integral locally Noetherian base, this quotient is also
identified with the Galois group of the induced function-field extension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- The finite quotient of the etale fundamental group represented by a
pointed finite-etale Galois cover. -/
noncomputable def finiteEtaleGaloisCoverQuotientMonoidHom
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    letI : IsGalois Y := hY
    π₁ᵉᵗ(xi) →* (Aut Y)ᵐᵒᵖ := by
  letI : IsGalois Y := hY
  exact galoisObjectQuotientMonoidHom
    (FiniteEtale.fiber xi) π₁ᵉᵗ(xi) Y y

@[simp]
theorem finiteEtaleGaloisCoverQuotientMonoidHom_evaluation
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) (g : π₁ᵉᵗ(xi)) :
    letI : IsGalois Y := hY
    (FiniteEtale.fiber xi).map
        ((finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y g).unop.hom) y =
      g • y := by
  let : IsGalois Y := hY
  exact galoisObjectQuotientMonoidHom_evaluation
    (FiniteEtale.fiber xi) π₁ᵉᵗ(xi) Y y g

/-- The pointed-cover quotient has kernel the stabilizer of the chosen
geometric fiber point. -/
theorem finiteEtaleGaloisCoverQuotientMonoidHom_ker
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    letI : IsGalois Y := hY
    (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y).ker =
      MulAction.stabilizer π₁ᵉᵗ(xi) y := by
  let : IsGalois Y := hY
  exact galoisObjectQuotientMonoidHom_ker
    (FiniteEtale.fiber xi) π₁ᵉᵗ(xi) Y y

/-- A pointed finite-etale Galois cover gives a surjective finite quotient
of the etale fundamental group. -/
theorem finiteEtaleGaloisCoverQuotientMonoidHom_surjective
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    letI : IsGalois Y := hY
    Function.Surjective
      (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y) := by
  let : IsGalois Y := hY
  exact galoisObjectQuotientMonoidHom_surjective
    (FiniteEtale.fiber xi) π₁ᵉᵗ(xi) Y y

/-- Every subgroup of the deck group is the image of its inverse image in
the pointed-cover fundamental-group quotient. -/
theorem finiteEtaleGaloisCoverQuotientMonoidHom_map_comap
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y)
    (H : Subgroup (Aut Y)ᵐᵒᵖ) :
    letI : IsGalois Y := hY
    Subgroup.map (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
        (Subgroup.comap
          (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y) H) = H := by
  let : IsGalois Y := hY
  exact Subgroup.map_comap_eq_self_of_surjective
    (finiteEtaleGaloisCoverQuotientMonoidHom_surjective xi Y hY y) H

/-- The function-field realization of the finite quotient represented by a
pointed finite-etale Galois cover. -/
noncomputable def finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    π₁ᵉᵗ(xi) →*
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) := by
  letI : IsGalois Y := hY
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).toMonoidHom.comp
    (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)

@[simp]
theorem finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_apply
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) (g : π₁ᵉᵗ(xi)) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom xi Y hY y g =
      finiteEtaleAutFunctionFieldAlgEquiv Y
        (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y g).unop := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact finiteEtaleAutOpFunctionFieldMulEquiv_apply Y hY _

/-- The function-field realization remains a surjective finite quotient. -/
theorem finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_surjective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Function.Surjective
      (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom xi Y hY y) := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).surjective.comp
    (finiteEtaleGaloisCoverQuotientMonoidHom_surjective xi Y hY y)

/-- Passing from the categorical cover quotient to the function-field
Galois group does not change its kernel. -/
theorem finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_ker
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom
      xi Y hY y).ker = MulAction.stabilizer π₁ᵉᵗ(xi) y := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  rw [finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom,
    MonoidHom.ker_comp_of_injective,
    finiteEtaleGaloisCoverQuotientMonoidHom_ker]
  exact (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).injective

end EtaleFundamentalGroups

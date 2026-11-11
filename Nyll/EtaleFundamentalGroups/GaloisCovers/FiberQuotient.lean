/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Category.FinTopCat

/-!
# Finite quotients represented by finite-etale Galois covers

A chosen point of the geometric fiber of a finite-etale Galois cover gives
the corresponding surjective finite quotient of the etale fundamental
group.  For a normal integral locally Noetherian base, this quotient is also
identified with the Galois group of the induced function-field extension.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

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
    let : IsGalois Y := hY
    π₁ᵉᵗ(xi) →* (Aut Y)ᵐᵒᵖ := by
  intro sharedDefinitionOwner1
  exact galoisObjectQuotientMonoidHom
    (FiniteEtale.fiber xi) π₁ᵉᵗ(xi) Y y

/-- The original pointed deck quotient is continuous for the discrete
finite deck-group topology. Its underlying homomorphism is unchanged. -/
noncomputable def finiteEtaleGaloisCoverQuotientHom
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y) (y : (FiniteEtale.fiber xi).obj Y)
    [TopologicalSpace (Aut Y)ᵐᵒᵖ] [DiscreteTopology (Aut Y)ᵐᵒᵖ] :
    π₁ᵉᵗ(xi) →ₜ* (Aut Y)ᵐᵒᵖ := by
  let : IsGalois Y := hY
  let F := FiniteEtale.fiber xi
  let e := evaluationEquivOfIsGalois F Y y
  refine ⟨finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y, ?_⟩
  change Continuous (fun g : π₁ᵉᵗ(xi) => MulOpposite.op (e.symm (g • y)))
  exact (continuous_of_discreteTopology (f := fun z : F.obj Y =>
    MulOpposite.op (e.symm z))).comp (continuous_id.smul continuous_const)

@[simp]
theorem finiteEtaleGaloisCoverQuotientMonoidHom_evaluation
    {X : Scheme.{u}} [ConnectedSpace X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) (g : π₁ᵉᵗ(xi)) :
    let : IsGalois Y := hY
    (FiniteEtale.fiber xi).map
        ((finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y g).unop.asIso.hom) y =
      g • y := by
  intro sharedOwner1
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
    let : IsGalois Y := hY
    (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y).ker =
      MulAction.stabilizer π₁ᵉᵗ(xi) y := by
  intro sharedOwner1
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
    let : IsGalois Y := hY
    Function.Surjective
      (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y) := by
  intro sharedOwner1
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
    let : IsGalois Y := hY
    Subgroup.map (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
        (Subgroup.comap
          (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y) H) = H := by
  intro sharedOwner1
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
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    π₁ᵉᵗ(xi) →*
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) := by
  intro sharedDefinitionOwner1 sharedDefinitionOwner2 sharedDefinitionOwner3
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
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom xi Y hY y g =
      finiteEtaleAutFunctionFieldAlgEquiv Y
        (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y g).unop := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  exact finiteEtaleAutOpFunctionFieldMulEquiv_apply Y hY _

/-- The function-field realization remains a surjective finite quotient. -/
theorem finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom_surjective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (y : (FiniteEtale.fiber xi).obj Y) :
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Function.Surjective
      (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom xi Y hY y) := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
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
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom
      xi Y hY y).ker = MulAction.stabilizer π₁ᵉᵗ(xi) y := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  rw [finiteEtaleGaloisCoverFunctionFieldQuotientMonoidHom,
    MonoidHom.ker_comp_of_injective,
    finiteEtaleGaloisCoverQuotientMonoidHom_ker]
  exact (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).injective

end EtaleFundamentalGroups

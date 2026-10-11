/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField

/-!
# Automorphisms of a Galois cover and of its function field

The pullback of rational functions is contravariant.  Accordingly, this
file compares the opposite of the categorical automorphism group of a
finite-etale Galois cover with the Galois group of its function field.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- Pullback of rational functions as a homomorphism from the opposite of
the automorphism group of a connected finite-etale cover. -/
noncomputable def finiteEtaleAutOpFunctionFieldMonoidHom
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (Aut Y)ᵐᵒᵖ →*
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) := by
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  letI : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  refine
    { toFun := fun σ ↦ finiteEtaleAutFunctionFieldAlgEquiv Y σ.unop
      map_one' := ?_
      map_mul' := ?_ }
  · have h := finiteEtaleAutFunctionFieldAlgEquiv_mul_rev Y
      (1 : Aut Y) (1 : Aut Y)
    let x := finiteEtaleAutFunctionFieldAlgEquiv Y (1 : Aut Y)
    have hx : x = x * x := by simpa only [one_mul] using h
    have hone : 1 = x := by
      simpa [mul_assoc] using
        congrArg (fun z ↦ x⁻¹ * z) hx
    exact hone.symm
  · intro σ τ
    change finiteEtaleAutFunctionFieldAlgEquiv Y (τ.unop * σ.unop) = _
    exact finiteEtaleAutFunctionFieldAlgEquiv_mul_rev Y τ.unop σ.unop

@[simp]
theorem finiteEtaleAutOpFunctionFieldMonoidHom_apply
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] (σ : (Aut Y)ᵐᵒᵖ) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    finiteEtaleAutOpFunctionFieldMonoidHom Y σ =
      finiteEtaleAutFunctionFieldAlgEquiv Y σ.unop := by
  unfold finiteEtaleAutOpFunctionFieldMonoidHom
  rfl

/-- The function-field action of cover automorphisms remains faithful after
passing to the opposite group. -/
theorem finiteEtaleAutOpFunctionFieldMonoidHom_injective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Function.Injective (finiteEtaleAutOpFunctionFieldMonoidHom Y) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  intro σ τ h
  apply MulOpposite.unop_injective
  apply finiteEtaleAutFunctionFieldAlgEquiv_injective Y
  simpa only [finiteEtaleAutOpFunctionFieldMonoidHom_apply] using h

/-- For a categorical Galois cover, its automorphism group has the degree of
the induced extension of function fields. -/
theorem natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Nat.card (Aut Y) =
      Module.finrank X.functionField Y.left.functionField := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : Algebra.IsSeparable X.functionField Y.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected Y
  let Ω := AlgebraicClosure X.functionField
  let ξ : Spec (.of Ω) ⟶ X := X.genericExtensionMorphism Ω
  let F := AlgebraicGeometry.FiniteEtale.fiber ξ
  let a : F.obj Y := Classical.choice inferInstance
  let e : F.obj Y ≃
      (Y.left.functionField →ₐ[X.functionField] Ω) :=
    (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom ξ Y).trans
      (finiteEtaleGenericHomEquivFunctionFieldAlgHom (Ω := Ω) Y)
  calc
    Nat.card (Aut Y) = Nat.card (F.obj Y) :=
      Nat.card_congr (evaluationEquivOfIsGalois F Y a)
    _ = Nat.card
        (Y.left.functionField →ₐ[X.functionField] Ω) := Nat.card_congr e
    _ = Module.finrank X.functionField Y.left.functionField :=
      AlgHom.natCard_of_splits X.functionField Y.left.functionField Ω
        (fun _ ↦ IsAlgClosed.splits _)

/-- A categorical finite-etale Galois cover supplies every automorphism of
its induced function-field extension. -/
theorem finiteEtaleAutOpFunctionFieldMonoidHom_surjective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Function.Surjective (finiteEtaleAutOpFunctionFieldMonoidHom Y) := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : Algebra.IsSeparable X.functionField Y.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois X.functionField Y.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  have hcardAut :=
    natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois Y hY
  have hcardDomain : Nat.card ((Aut Y)ᵐᵒᵖ) =
      Module.finrank X.functionField Y.left.functionField := by
    rw [Nat.card_congr MulOpposite.opEquiv.symm]
    exact hcardAut
  have hcardCodomain : Nat.card
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) =
      Module.finrank X.functionField Y.left.functionField :=
    _root_.IsGalois.card_aut_eq_finrank
      X.functionField Y.left.functionField
  exact ((finiteEtaleAutOpFunctionFieldMonoidHom_injective Y).bijective_of_nat_card_le
    (by rw [hcardDomain, hcardCodomain])).surjective

/-- The opposite categorical automorphism group of a finite-etale Galois
cover is canonically the Galois group of its function field. -/
noncomputable def finiteEtaleAutOpFunctionFieldMulEquiv
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (Aut Y)ᵐᵒᵖ ≃*
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) := by
  letI : IsGalois Y := hY
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact MulEquiv.ofBijective (finiteEtaleAutOpFunctionFieldMonoidHom Y)
    ⟨finiteEtaleAutOpFunctionFieldMonoidHom_injective Y,
      finiteEtaleAutOpFunctionFieldMonoidHom_surjective Y hY⟩

@[simp]
theorem finiteEtaleAutOpFunctionFieldMulEquiv_apply
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) (σ : (Aut Y)ᵐᵒᵖ) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    finiteEtaleAutOpFunctionFieldMulEquiv Y hY σ =
      finiteEtaleAutFunctionFieldAlgEquiv Y σ.unop := by
  change finiteEtaleAutOpFunctionFieldMonoidHom Y σ = _
  exact finiteEtaleAutOpFunctionFieldMonoidHom_apply Y σ

end EtaleFundamentalGroups

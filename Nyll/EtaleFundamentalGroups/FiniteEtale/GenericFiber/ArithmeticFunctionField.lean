/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.ArithmeticGenericFiber
public import Nyll.SchemeTheory.FunctionFields.IntegerBaseChange
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FractionFieldTensorDomain
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Geometric integrality of arithmetic function fields

An affine open of an integral arithmetic scheme stays nonempty after a
characteristic-zero field extension: its coordinate ring embeds in the tensor
product. Geometric integrality of the generic fiber then makes this tensor
product a domain. Passing to the fraction field gives the corresponding
rational tensor product of function fields.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

attribute [local instance] uliftIntegerBaseIsDomain ULift.algebra'

namespace EtaleFundamentalGroups

/-- The function field of an integral arithmetic scheme with geometrically
integral generic fiber remains a domain after every characteristic-zero
field extension of its rational constants. -/
theorem isDomain_functionField_ratTensor_of_arithmetic_genericFiber
    {X : Scheme.{u}} [IsIntegral X] [CharZero X.functionField]
    (f : X ⟶ Spec (.of (ULift.{u} ℤ)))
    [GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint (Spec (.of (ULift.{u} ℤ)))))]
    (K : Type u) [Field K] [CharZero K] :
    IsDomain (X.functionField ⊗[ℚ] K) := by
  let x : X := genericPoint X
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U :=
    isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))
  let : Nonempty U := ⟨⟨x, X.affineCover.covers x⟩⟩
  let B := Γ(X, U)
  let : IsFractionRing B X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : Module.IsTorsionFree ℤ B :=
    Module.IsTorsionFree.of_faithfulSMul B ℤ X.functionField
  have : Module.Flat ℤ B := inferInstance
  have hinj : Function.Injective (algebraMap B (B ⊗[ℤ] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := ℤ) (A := B)
      (Int.cast_injective (α := K))
  let : Nontrivial (B ⊗[ℤ] K) := hinj.nontrivial
  let eTensor : (B ⊗[ULift.{u} ℤ] K) ≃ₐ[ℤ] (B ⊗[ℤ] K) :=
    intTensorULiftBaseEquiv B K
  let : Nontrivial (B ⊗[ULift.{u} ℤ] K) := eTensor.symm.injective.nontrivial
  let i : Spec (.of B) ⟶ X := hU.isoSpec.inv ≫ U.ι
  let g : Spec (.of K) ⟶ Spec (.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) K))
  have hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) B)) :=
    specULiftZIsTerminal.hom_ext _ _
  let e : pullback (i ≫ f) g ≅ Spec (.of (B ⊗[ULift.{u} ℤ] K)) := by
    rw [hi]
    exact pullbackSpecIso (ULift.{u} ℤ) B K
  let j : pullback (i ≫ f) g ⟶ pullback f g :=
    pullback.map (i ≫ f) g f g i (𝟙 _) (𝟙 _)
      (Category.comp_id _).symm (by rw [Category.id_comp, Category.comp_id])
  let : IsOpenImmersion i := inferInstance
  let : IsOpenImmersion j :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstance : IsOpenImmersion i)
      (inferInstance : IsOpenImmersion (𝟙 (Spec (.of K))))
      rfl (Category.id_comp g).symm
  let : Nonempty ↥(pullback (i ≫ f) g) :=
    ⟨e.inv (Nonempty.some (inferInstance : Nonempty (Spec (.of (B ⊗[ULift.{u} ℤ] K)))))⟩
  let : GeometricallyIntegral (pullback.snd f g) :=
    geometricallyIntegral_pullback_of_arithmetic_genericFiber f K
  let : IsIntegral (pullback f g) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f g)
  let : IsIntegral (pullback (i ≫ f) g) := isIntegral_of_isOpenImmersion j
  let : IsIntegral (Spec (.of (B ⊗[ULift.{u} ℤ] K))) := IsIntegral.of_isIso e.hom
  let : IsDomain (B ⊗[ULift.{u} ℤ] K) :=
    (affine_isIntegral_iff (.of (B ⊗[ULift.{u} ℤ] K))).mp inferInstance
  let : IsDomain (B ⊗[ℤ] K) := eTensor.toRingEquiv.symm.toMulEquiv.isDomain _
  exact Algebra.TensorProduct.isDomain_ratTensor_of_isFractionRing_intTensor
    (B := B) (F := X.functionField) (K := K)

end EtaleFundamentalGroups

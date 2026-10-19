/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.ArithmeticGenericFiber
import Nyll.SchemeTheory.RingTheory.FieldExtensions.FractionFieldTensorDomain
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Geometric integrality of arithmetic function fields

An affine open of an integral arithmetic scheme stays nonempty after a
characteristic-zero field extension: its coordinate ring embeds in the tensor
product. Geometric integrality of the generic fiber then makes this tensor
product a domain. Passing to the fraction field gives the corresponding
rational tensor product of function fields.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace EtaleFundamentalGroups

/-- The function field of an integral arithmetic scheme with geometrically
integral generic fiber remains a domain after every characteristic-zero
field extension of its rational constants. -/
theorem isDomain_functionField_ratTensor_of_arithmetic_genericFiber
    {X : Scheme} [IsIntegral X] [CharZero X.functionField]
    (f : X ⟶ Spec (.of ℤ))
    [GeometricallyIntegral
      (f.fiberToSpecResidueField (genericPoint (Spec (.of ℤ))))]
    (K : Type) [Field K] [CharZero K] :
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
  let i : Spec (.of B) ⟶ X := hU.isoSpec.inv ≫ U.ι
  let g : Spec (.of K) ⟶ Spec (.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ K))
  have hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) :=
    specZIsTerminal.hom_ext _ _
  let e : pullback (i ≫ f) g ≅ Spec (.of (B ⊗[ℤ] K)) := by
    rw [hi]
    exact pullbackSpecIso ℤ B K
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
    ⟨e.inv (Nonempty.some (inferInstance : Nonempty (Spec (.of (B ⊗[ℤ] K)))))⟩
  let : GeometricallyIntegral (pullback.snd f g) :=
    geometricallyIntegral_pullback_of_arithmetic_genericFiber f K
  let : IsIntegral (pullback f g) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f g)
  let : IsIntegral (pullback (i ≫ f) g) := isIntegral_of_isOpenImmersion j
  let : IsIntegral (Spec (.of (B ⊗[ℤ] K))) := IsIntegral.of_isIso e.hom
  let : IsDomain (B ⊗[ℤ] K) :=
    (affine_isIntegral_iff (.of (B ⊗[ℤ] K))).mp inferInstance
  exact Algebra.TensorProduct.isDomain_ratTensor_of_isFractionRing_intTensor
    (B := B) (F := X.functionField) (K := K)

end EtaleFundamentalGroups

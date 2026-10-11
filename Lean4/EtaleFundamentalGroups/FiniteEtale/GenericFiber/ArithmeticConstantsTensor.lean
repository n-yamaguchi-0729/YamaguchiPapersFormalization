/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Dominance after adjoining arithmetic constants

An integral subring of a geometrically integral function field remains
disjoint from the integers of a number field. This proves injectivity of
the actual multiplication map used in the arithmetic constants argument.
-/

noncomputable section

open scoped TensorProduct NumberField

namespace EtaleFundamentalGroups

/-- Algebraic integers in a constant subfield lie in a normal domain with
the given fraction field. The map is constructed by restricting to the
range of the original inclusion into the fraction field. -/
def ringOfIntegersToNormalDomain
    (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [NumberField K] [Field L] [CharZero L]
    [Algebra A L] [IsFractionRing A L] (g : K →ₐ[ℚ] L) :
    𝓞 K →ₐ[ℤ] A :=
  let a : A →ₐ[ℤ] L := IsScalarTower.toAlgHom ℤ A L
  let k : 𝓞 K →ₐ[ℤ] L :=
    (g.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
  (AlgEquiv.ofInjective a (IsFractionRing.injective A L)).symm.toAlgHom.comp
    (k.codRestrict a.range (fun z ↦ by
      have hz : IsIntegral ℤ (k z) :=
        (isIntegral_algHom_iff (g.restrictScalars ℤ) g.injective).mpr z.property
      exact IsIntegrallyClosed.algebraMap_eq_of_integral (hz.tower_top (A := A))))

/-- The constructed map of integer rings has the prescribed value in the
original fraction field. -/
theorem algebraMap_ringOfIntegersToNormalDomain
    (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [NumberField K] [Field L] [CharZero L]
    [Algebra A L] [IsFractionRing A L] (g : K →ₐ[ℚ] L) (z : 𝓞 K) :
    algebraMap A L (ringOfIntegersToNormalDomain A K L g z) = g (z : K) := by
  let a : A →ₐ[ℤ] L := IsScalarTower.toAlgHom ℤ A L
  let k : 𝓞 K →ₐ[ℤ] L :=
    (g.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
  let e : A ≃ₐ[ℤ] a.range :=
    AlgEquiv.ofInjective a (IsFractionRing.injective A L)
  change ((e (ringOfIntegersToNormalDomain A K L g z) : a.range) : L) = k z
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- An integral constant extension embeds in a common overfield when the
corresponding rational tensor product is a domain. -/
theorem arithmeticConstantsTensor_lift_injective
    {B F K L : Type} [CommRing B] [Field F] [CharZero F]
    [Field K] [NumberField K] [Field L] [CharZero L]
    (i : B →ₐ[ℤ] F) (hi : Function.Injective i)
    (f : F →ₐ[ℚ] L) (g : K →ₐ[ℚ] L)
    [IsDomain (F ⊗[ℚ] K)] :
    Function.Injective (Algebra.TensorProduct.lift
      ((f.restrictScalars ℤ).comp i)
      ((g.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
      (fun _ _ ↦ Commute.all _ _)) := by
  let j : 𝓞 K →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  let m : B ⊗[ℤ] (𝓞 K) →ₐ[ℤ] F ⊗[ℤ] K :=
    Algebra.TensorProduct.map i j
  have hm : Function.Injective m := by
    exact TensorProduct.map_injective_of_flat_flat i.toLinearMap j.toLinearMap
      hi (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  let e : F ⊗[ℚ] K ≃ₐ[ℚ] F ⊗[ℤ] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors ℤ) ℚ F K
  let h : F ⊗[ℚ] K →ₐ[ℚ] L :=
    Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)
  have hfield : IsField (F ⊗[ℚ] K) :=
    Algebra.TensorProduct.isField_of_isAlgebraic ℚ F K (.inr inferInstance)
  let : Field (F ⊗[ℚ] K) := hfield.toField
  have hh : Function.Injective h := h.injective
  have heq : (h.restrictScalars ℤ).comp ((e.symm.restrictScalars ℤ).toAlgHom.comp m) =
      Algebra.TensorProduct.lift ((f.restrictScalars ℤ).comp i)
        ((g.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
        (fun _ _ ↦ Commute.all _ _) := by
    ext b <;> rfl
  rw [← heq]
  exact hh.comp (e.symm.injective.comp hm)

end EtaleFundamentalGroups

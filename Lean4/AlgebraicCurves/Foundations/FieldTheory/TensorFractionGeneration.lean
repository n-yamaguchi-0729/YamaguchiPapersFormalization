/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Generators of the fraction field of a scalar extension

The fraction field of a scalar-extended affine coordinate ring is generated
by the new constants and the image of the old function field. This lemma
uses the tensor-product description of the coordinate ring, rather than
assuming generation of the function field.
-/

open scoped TensorProduct

namespace IntermediateField

/-- An affine tensor-product presentation supplies the field-generation
condition for constant extension. -/
theorem adjoin_range_eq_top_of_tensor_fraction
    {K K' F L A B : Type*}
    [Field K] [Field K'] [Field F] [Field L]
    [CommRing A] [CommRing B] [Algebra K K'] [Algebra K A]
    [Algebra K' B] [Algebra B L] [Algebra K' L] [IsScalarTower K' B L]
    [IsFractionRing B L]
    (e : K' ⊗[K] A ≃ₐ[K'] B)
    (a : A →+* F) (φ : F →+* L)
    (h : ∀ x : A, algebraMap B L (e (1 ⊗ₜ[K] x)) = φ (a x)) :
    IntermediateField.adjoin K' (Set.range φ) = ⊤ := by
  let E := IntermediateField.adjoin K' (Set.range φ)
  have hmem : ∀ t : K' ⊗[K] A, algebraMap B L (e t) ∈ E := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c x =>
      have ht : c ⊗ₜ[K] x =
          algebraMap K' (K' ⊗[K] A) c * (1 ⊗ₜ[K] x) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht, map_mul, map_mul, e.commutes, ← IsScalarTower.algebraMap_apply, h]
      exact E.mul_mem (E.algebraMap_mem c) (IntermediateField.subset_adjoin K' _ ⟨a x, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact E.add_mem hx hy
  apply top_unique
  intro z _
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  exact E.div_mem (by simpa only [e.apply_symm_apply] using hmem (e.symm x))
    (by simpa only [e.apply_symm_apply] using hmem (e.symm y))

end IntermediateField

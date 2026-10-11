/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Transporting tensor-product surjectivity

This file provides a small algebraic bridge used when a geometric pullback
describes a tensor product in the order opposite to the desired function-
field tensor product.  Surjectivity is transported using equivalences of the
two factors and of the target; compatibility only has to be checked on pure
tensors.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

/-- A surjective map out of a reversed tensor product gives surjectivity of
the desired product map, provided the factor identifications agree on pure
tensors. -/
theorem productMap_surjective_of_surjective_reversed_tensor
    {R : Type u₁} {A : Type u₂} {B : Type u₃} {C : Type u₄}
    {R' : Type u₅} {A' : Type u₆} {B' : Type u₇} {C' : Type u₈}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [CommRing R'] [CommRing A'] [CommRing B'] [CommRing C']
    [Algebra R A] [Algebra R B] [Algebra R C]
    [Algebra R' A'] [Algebra R' B']
    (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (q : B' ⊗[R'] A' →+* C')
    (eA : A ≃+* A') (eB : B ≃+* B') (eC : C' ≃+* C)
    (hq : Function.Surjective q)
    (hpure : ∀ (a : A) (b : B),
      eC (q (eB b ⊗ₜ[R'] eA a)) = f a * g b) :
    Function.Surjective (productMap f g) := by
  have hlift (z : B' ⊗[R'] A') :
      ∃ x : A ⊗[R] B, productMap f g x = eC (q z) := by
    induction z using TensorProduct.inductionOn with
    | tmul b' a' =>
        refine ⟨eA.symm a' ⊗ₜ[R] eB.symm b', ?_⟩
        simpa using (hpure (eA.symm a') (eB.symm b')).symm
    | add x y hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        refine ⟨x' + y', ?_⟩
        rw [map_add, map_add, map_add, hx', hy']
  intro c
  obtain ⟨z, hz⟩ := hq (eC.symm c)
  obtain ⟨x, hx⟩ := hlift z
  refine ⟨x, hx.trans ?_⟩
  rw [hz]
  exact eC.apply_symm_apply c

end Algebra.TensorProduct

end

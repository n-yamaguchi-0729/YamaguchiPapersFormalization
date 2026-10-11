/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Separation by an injective module containing the residue field

A nonzero element generates a cyclic module whose defining ideal is
contained in the maximal ideal.  Its quotient onto the residue field,
followed by the given embedding, extends to the entire module by
injectivity.  Thus maps to the injective module separate elements, and
the associated evaluation map into the double dual is injective.
-/

namespace EtaleFundamentalGroups.Purity

universe u v w

open IsLocalRing

/-- Evaluation into the double dual with values in a fixed module. -/
def residueFieldHullEvaluation (R : Type u) (E : Type v) (M : Type w)
    [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] : M →ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearMap.flip (LinearMap.id : (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E))

theorem residueFieldHullEvaluation_apply
    (R : Type u) (E : Type v) (M : Type w)
    [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M] (x : M) (f : M →ₗ[R] E) :
    residueFieldHullEvaluation R E M x f = f x := rfl

variable {R E : Type u} [CommRing R] [IsLocalRing R]
variable [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- Maps into an injective module containing the residue field detect every
nonzero element.  Essentiality of the residue-field image is not needed. -/
theorem exists_linearMap_apply_ne_zero_of_injective_residueField
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    {M : Type v} [AddCommGroup M] [Module R M] (x : M) (hx : x ≠ 0) :
    ∃ f : M →ₗ[R] E, f x ≠ 0 := by
  let a : R →ₗ[R] M := LinearMap.toSpanSingleton R M x
  have ha1 : a 1 = x := LinearMap.toSpanSingleton_apply_one R M x
  have hkerproper : LinearMap.ker a ≠ ⊤ := by
    intro h
    have hazero : a = 0 := LinearMap.ker_eq_top.mp h
    have hz : a 1 = 0 := DFunLike.congr_fun hazero 1
    exact hx (ha1.symm.trans hz)
  have hker : LinearMap.ker a ≤ maximalIdeal R := le_maximalIdeal hkerproper
  let g : LinearMap.range a →ₗ[R] E :=
    i.comp ((Submodule.factor hker).comp a.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨f, hf⟩ := Module.Injective.extension_property R E (LinearMap.range a) M
    (LinearMap.range a).subtype (LinearMap.range a).injective_subtype g
  have hf1 : f (a 1) = i ((maximalIdeal R).mkQ 1) := by
    have h := DFunLike.congr_fun hf ⟨a 1, LinearMap.mem_range_self a 1⟩
    change f (a 1) = i (Submodule.factor hker
      (a.quotKerEquivRange.symm ⟨a 1, LinearMap.mem_range_self a 1⟩)) at h
    rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.factor_mk] at h
    exact h
  refine ⟨f, ?_⟩
  intro hfx
  have h10 : i (1 : R ⧸ maximalIdeal R) = i 0 := by
    rw [map_zero]
    change i ((maximalIdeal R).mkQ 1) = 0
    rw [← hf1, ha1, hfx]
  exact one_ne_zero (hi h10)

/-- Evaluation into the double dual is injective when the target is
injective and contains the residue field. -/
theorem injective_eval_to_injective_residueField
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (residueFieldHullEvaluation R E M) := by
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨f, hf⟩ :=
    exists_linearMap_apply_ne_zero_of_injective_residueField i hi (x - y) hne
  apply hf
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun hxy f)

end EtaleFundamentalGroups.Purity

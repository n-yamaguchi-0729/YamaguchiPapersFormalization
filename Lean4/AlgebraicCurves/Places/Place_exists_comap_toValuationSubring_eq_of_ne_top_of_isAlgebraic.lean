/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Place_exists_of_valuationSubring_of_finiteDimensional

/-!
# Place exists comap to Valuation Subring eq of ne top of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
    {κ : Type*} [Field κ] {k : Type*} [Field k] {E : Type*} [Field E]
    [Algebra κ k] [Algebra k E] [Algebra κ E] [IsScalarTower κ k E] [Algebra.IsAlgebraic k E]
    (x : E) [FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set E)) E]
    (W : ValuationSubring k) (hW : W ≠ ⊤) (hκ : ∀ a : κ, algebraMap κ k a ∈ W) :
    ∃ w : AlgebraicCurve.Place κ E, w.toValuationSubring.comap (algebraMap k E) = W := by
  classical
  set f : k →+* E := algebraMap k E with hf_def
  have hf : Function.Injective f := (algebraMap k E).injective
  let A : LocalSubring E := (W.toLocalSubring).map f
  obtain ⟨V, hAV⟩ := A.exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hAV
  have hAdef : A.toSubring = W.toSubring.map f := rfl
  have hmemV : ∀ y : k, y ∈ W → f y ∈ V := fun y hy => hle ⟨y, hy, rfl⟩
  have hcomap : V.comap f = W := by
    ext y
    rw [ValuationSubring.mem_comap]
    refine ⟨fun hy => ?_, hmemV y⟩
    by_contra hyW
    have hy0 : y ≠ 0 := fun h => hyW (h ▸ W.zero_mem)
    have hyinv : y⁻¹ ∈ W := (W.mem_or_inv_mem y).resolve_left hyW
    have hnu : ¬ IsUnit (⟨y⁻¹, hyinv⟩ : W) := by
      rintro ⟨u, hu⟩
      have h0 : ((u⁻¹ : Wˣ) : W) * ⟨y⁻¹, hyinv⟩ = 1 := by rw [← hu]; exact u.inv_mul
      have h1 : (((u⁻¹ : Wˣ) : W) : k) * y⁻¹ = 1 := by
        have := congrArg Subtype.val h0
        simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
      have h2 : (((u⁻¹ : Wˣ) : W) : k) = y := (mul_inv_eq_one₀ hy0).mp h1
      exact hyW (h2 ▸ ((u⁻¹ : Wˣ) : W).2)
    have hunitV : IsUnit (Subring.inclusion hle ⟨f y⁻¹, ⟨y⁻¹, hyinv, rfl⟩⟩) := by
      refine ⟨⟨⟨f y⁻¹, hmemV _ hyinv⟩, ⟨f y, hy⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext; change f y⁻¹ * f y = 1; rw [← map_mul, inv_mul_cancel₀ hy0, map_one]
      · apply Subtype.ext; change f y * f y⁻¹ = 1; rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
    have hunitA : IsUnit (⟨f y⁻¹, ⟨y⁻¹, hyinv, rfl⟩⟩ : A.toSubring) := hloc.map_nonunit _ hunitV
    let e : W.toSubring ≃+* W.toSubring.map f := W.toSubring.equivMapOfInjective f hf
    have he : e ⟨y⁻¹, hyinv⟩ = (⟨f y⁻¹, ⟨y⁻¹, hyinv, rfl⟩⟩ : W.toSubring.map f) := Subtype.ext rfl
    have hunitW : IsUnit (⟨y⁻¹, hyinv⟩ : W) := by
      have h3 : IsUnit (e ⟨y⁻¹, hyinv⟩) := by rw [he]; exact hunitA
      have h4 := h3.map e.symm.toRingHom
      simpa using h4
    exact hnu hunitW
  have hVtop : V ≠ ⊤ := by
    intro hV
    apply hW
    rw [← hcomap, hV]
    ext y; simp [ValuationSubring.mem_comap, ValuationSubring.mem_top]
  have hVκ : ∀ a : κ, algebraMap κ E a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply κ k E]; exact hmemV _ (hκ a)
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x V hVκ
    hVtop
  exact ⟨w, by rw [hw, hcomap]⟩
end AlgebraicCurves.Places.Proofs.Place_exists_comap_toValuationSubring_eq_of_ne_top_of_isAlgebraic
end ProofImplementation

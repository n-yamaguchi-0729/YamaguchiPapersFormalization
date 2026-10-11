/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Cartier

/-!
# Cancellation by an invertible ideal sheaf

Multiplication by an invertible ideal sheaf can be cancelled from equality of ideal-sheaf
products, using local non-zero-divisor generators.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_IsInvertible_mul_left_cancel

universe u

namespace Ideal
open _root_.Ideal
end Ideal
open scoped _root_.Ideal in
theorem Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors {R : Type*} [CommRing R]
    {a : R} (ha : a ∈ nonZeroDivisors R) :
    Function.Injective fun K : Ideal R ↦ Ideal.span {a} * K := by
  suffices key : ∀ K K' : Ideal R, Ideal.span {a} * K = Ideal.span {a} * K' → K ≤ K' from
    fun K K' h ↦ le_antisymm (key K K' h) (key K' K h.symm)
  intro K K' h x hx
  have hax : a * x ∈ Ideal.span {a} * K' := h ▸ Ideal.mem_span_singleton_mul.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Ideal.mem_span_singleton_mul.mp hax
  rwa [← (mul_cancel_left_mem_nonZeroDivisors ha).mp hyx]

open AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.mul_left_cancel {X : Scheme.{u}}
    {I J J' : X.IdealSheafData} (hI : I.IsInvertible) (h : I * J = I * J') : J = J' := by
  choose U f hxf g hg hIg using hI
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x : X ↦ X.affineBasicOpen (f x)) ?_ ?_
  · exact top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxf x⟩
  · intro x
    have hx := congrArg (fun K : X.IdealSheafData ↦ K.ideal (X.affineBasicOpen (f x))) h
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hIg] at hx
    exact Ideal.span_singleton_mul_right_injective_of_mem_nonZeroDivisors (hg x) hx
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_IsInvertible_mul_left_cancel
end ProofImplementation

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Excluding the multiplier as an eigenvalue of a similitude

For a nondegenerate bilinear pairing with multiplier `c`, the absence of
fixed vectors in finite dimension excludes eigenvectors of eigenvalue `c`.
The proof uses the surjectivity of `F - 1` and does not require an
eigenvalue splitting field or a diagonalization assumption.

In arithmetic applications the pairing is the Weil pairing and `F` is a
good-reduction Frobenius. This file proves only the linear algebra;
good reduction and the absence of fixed vectors must be proved separately.
-/

namespace AnabelianGeometry.GaloisRepresentations

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- If `F - 1` is surjective, a nondegenerate similitude has no eigenvector
for its nonzero multiplier. -/
theorem eq_zero_of_similitude_eigenvector
    (B : LinearMap.BilinForm K V) (hB : Function.Injective B)
    (F : V →ₗ[K] V) (c : K) (hc : c ≠ 0)
    (hpair : ∀ x y : V, B (F x) (F y) = c * B x y)
    (hsurj : Function.Surjective (F - (LinearMap.id : V →ₗ[K] V)))
    {v : V} (hv : F v = c • v) : v = 0 := by
  apply hB
  ext w
  rw [LinearMap.BilinForm.zero_left]
  obtain ⟨y, hy⟩ := hsurj w
  change F y - y = w at hy
  have heq : B v (F y) = B v y := by
    have h := hpair v y
    rw [hv, LinearMap.BilinForm.smul_left] at h
    exact mul_left_cancel₀ hc h
  rw [← hy, LinearMap.BilinForm.sub_right, heq, sub_self]

/-- In finite dimension, absence of fixed vectors excludes the multiplier
eigenspace of a nondegenerate similitude. -/
theorem eq_zero_of_similitude_eigenvector_of_no_fixed_vectors
    [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : Function.Injective B)
    (F : V →ₗ[K] V) (c : K) (hc : c ≠ 0)
    (hpair : ∀ x y : V, B (F x) (F y) = c * B x y)
    (hfixed : ∀ x : V, F x = x → x = 0)
    {v : V} (hv : F v = c • v) : v = 0 := by
  have hinj : Function.Injective (F - (LinearMap.id : V →ₗ[K] V)) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    rw [LinearMap.mem_ker] at hx
    change F x - x = 0 at hx
    rw [Submodule.mem_bot]
    exact hfixed x (sub_eq_zero.mp hx)
  exact eq_zero_of_similitude_eigenvector B hB F c hc hpair
    (LinearMap.surjective_of_injective hinj) hv

end AnabelianGeometry.GaloisRepresentations

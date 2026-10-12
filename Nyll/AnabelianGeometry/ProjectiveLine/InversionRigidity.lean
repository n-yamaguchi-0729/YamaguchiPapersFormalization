/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rigidity of a parameter and its complement under inversion

If both a parameter and its complement are known up to inversion, the only
possible ambiguity lies on the polynomial `X² - X + 1`. These field identities
are independent of the arithmetic mechanism that reconstructs the parameters.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u

variable {K : Type u} [Field K]

/-- Simultaneous inversion of a parameter and its complement forces the
sixth-cyclotomic polynomial to vanish. -/
theorem sq_sub_add_one_eq_zero_of_complement_inv {x : K}
    (hx : x ≠ 0) (hx1 : x ≠ 1) (h : 1 - x⁻¹ = (1 - x)⁻¹) :
    x ^ 2 - x + 1 = 0 := by
  have hc : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hp : (1 - x⁻¹) * (1 - x) = 1 := by
    rw [h]
    exact inv_mul_cancel₀ hc
  calc
    x ^ 2 - x + 1 = x - x * ((1 - x⁻¹) * (1 - x)) := by
      field_simp [hx]
      ring
    _ = 0 := by rw [hp, mul_one, sub_self]

/-- A parameter and its complement, each determined up to inversion, determine
that parameter except on an explicit quadratic locus. -/
theorem eq_or_sq_sub_add_one_eq_zero_of_inversion_choices {x y : K}
    (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hxy : y = x ∨ y = x⁻¹)
    (hc : 1 - y = 1 - x ∨ 1 - y = (1 - x)⁻¹) :
    y = x ∨ x ^ 2 - x + 1 = 0 := by
  rcases hxy with hxy | hxy
  · exact Or.inl hxy
  rcases hc with hc | hc
  · exact Or.inl (sub_right_injective hc)
  · right
    rw [hxy] at hc
    exact sq_sub_add_one_eq_zero_of_complement_inv hx hx1 hc

/-- Away from the quadratic exceptional locus, the two inversion choices
recover the parameter uniquely. -/
theorem eq_of_inversion_choices {x y : K}
    (hx : x ≠ 0) (hx1 : x ≠ 1) (he : x ^ 2 - x + 1 ≠ 0)
    (hxy : y = x ∨ y = x⁻¹)
    (hc : 1 - y = 1 - x ∨ 1 - y = (1 - x)⁻¹) : y = x := by
  rcases eq_or_sq_sub_add_one_eq_zero_of_inversion_choices hx hx1 hxy hc with h | h
  · exact h
  · exact False.elim (he h)

/-- In characteristic different from two, a square root of an exceptional
parameter lies outside the same exceptional locus. -/
theorem sq_sub_add_one_ne_zero_of_sq_eq {x t : K}
    (h2 : (2 : K) ≠ 0) (hx : x ^ 2 - x + 1 = 0) (ht : t ^ 2 = x) :
    t ^ 2 - t + 1 ≠ 0 := by
  intro he
  rw [← ht] at hx
  have hp : (2 : K) * (1 - t) = 0 := by
    linear_combination hx - (t ^ 2 + t - 1) * he
  have ht1 : t = 1 := (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left h2)).symm
  rw [ht1] at he
  norm_num at he

end AnabelianGeometry.ProjectiveLine

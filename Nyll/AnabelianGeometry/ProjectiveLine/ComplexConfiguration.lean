/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The unit-circle exceptional locus

A complex parameter whose value and complement both have norm one lies
on the quadratic exceptional locus. This supplies the archimedean step
for the simultaneous torsion case in multiplicative reconstruction.
-/

namespace AnabelianGeometry.ProjectiveLine

/-- Two unit-circle conditions force the sixth-cyclotomic quadratic. -/
theorem sq_sub_add_one_eq_zero_of_norm_eq_one {z : ℂ}
    (hz : ‖z‖ = 1) (hc : ‖1 - z‖ = 1) : z ^ 2 - z + 1 = 0 := by
  have hnorm := Complex.sq_norm z
  have hcomp := Complex.sq_norm (1 - z)
  simp only [hz, one_pow, Complex.normSq_apply] at hnorm
  simp only [hc, one_pow, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, zero_sub] at hcomp
  have hre : 2 * z.re = 1 := by nlinarith [hnorm, hcomp]
  apply Complex.ext
  · simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.one_re, Complex.zero_re]
    nlinarith [hnorm, hre]
  · simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.one_im, Complex.zero_im, add_zero]
    linear_combination z.im * hre

/-- A complex parameter and its complement cannot both be torsion outside
the quadratic exceptional locus. -/
theorem sq_sub_add_one_eq_zero_of_isOfFinOrder {z : ℂ}
    (hz : IsOfFinOrder z) (hc : IsOfFinOrder (1 - z)) : z ^ 2 - z + 1 = 0 := by
  obtain ⟨n, hn, hzn⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  obtain ⟨m, hm, hcm⟩ := isOfFinOrder_iff_pow_eq_one.mp hc
  exact sq_sub_add_one_eq_zero_of_norm_eq_one
    (Complex.norm_eq_one_of_pow_eq_one hzn hn.ne')
    (Complex.norm_eq_one_of_pow_eq_one hcm hm.ne')

/-- The torsion exceptional-locus calculation descends through any complex
embedding, in particular through an embedding of a number field. -/
theorem sq_sub_add_one_eq_zero_of_isOfFinOrder_of_embedding
    {K : Type*} [Field K] (e : K →+* ℂ) {x : K}
    (hx : IsOfFinOrder x) (hc : IsOfFinOrder (1 - x)) : x ^ 2 - x + 1 = 0 := by
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  obtain ⟨m, hm, hcm⟩ := isOfFinOrder_iff_pow_eq_one.mp hc
  have hz : (e x) ^ n = 1 := by rw [← map_pow, hxn, map_one]
  have hz' : (1 - e x) ^ m = 1 := by
    rw [← map_one e, ← map_sub, ← map_pow, hcm, map_one]
  apply e.injective
  rw [map_add, map_sub, map_pow, map_one, map_zero]
  exact sq_sub_add_one_eq_zero_of_norm_eq_one
    (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')
    (Complex.norm_eq_one_of_pow_eq_one hz' hm.ne')

/-- If the complements of a nonzero parameter and its inverse both have
norm one, that parameter lies on the same quadratic exceptional locus. -/
theorem sq_sub_add_one_eq_zero_of_complement_norms {z : ℂ} (hz : z ≠ 0)
    (hc : ‖1 - z‖ = 1) (hi : ‖1 - z⁻¹‖ = 1) : z ^ 2 - z + 1 = 0 := by
  have he : 1 - z⁻¹ = -(1 - z) / z := by
    field_simp [hz]
    ring
  rw [he, norm_div, norm_neg, hc] at hi
  have hn : ‖z‖ = 1 := by
    apply inv_eq_one.mp
    simpa only [one_div] using hi
  exact sq_sub_add_one_eq_zero_of_norm_eq_one hn hc

end AnabelianGeometry.ProjectiveLine

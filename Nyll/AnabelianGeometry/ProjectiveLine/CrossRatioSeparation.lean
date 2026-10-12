/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.CrossRatio
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Separation of projective points by a cross ratio

For a fixed nondegenerate ordered triple, the cross ratio separates fourth
points in its affine chart. This is proved for homogeneous representatives
and then for the actual projectivization quotient.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u

variable {K : Type u} [Field K]

/-- Equal cross ratios force the two fourth representatives to be collinear. -/
theorem bracket_eq_zero_of_homogeneousCrossRatio_eq (a b c d e : K × K)
    (hba : bracket b a ≠ 0) (hca : bracket c a ≠ 0) (hcb : bracket c b ≠ 0)
    (hdb : bracket d b ≠ 0) (heb : bracket e b ≠ 0)
    (h : homogeneousCrossRatio a b c d = homogeneousCrossRatio a b c e) :
    bracket d e = 0 := by
  have hm := (div_eq_div_iff (mul_ne_zero hdb hca) (mul_ne_zero heb hca)).mp h
  have hp : (bracket d a * bracket e b - bracket e a * bracket d b) *
      (bracket c b * bracket c a) = 0 := by
    linear_combination hm
  have hz : bracket d a * bracket e b - bracket e a * bracket d b = 0 :=
    (mul_eq_zero.mp hp).resolve_right (mul_ne_zero hcb hca)
  have hr : bracket d e * bracket b a = 0 := by
    rw [← bracket_crossRatio_relation a b e d]
    linear_combination -hz
  exact (mul_eq_zero.mp hr).resolve_right hba

/-- Collinear homogeneous vectors are explicitly proportional on a bracket chart. -/
theorem eq_smul_of_bracket_eq_zero (a b c : K × K)
    (hac : bracket a c ≠ 0) (hab : bracket a b = 0) :
    b = (bracket b c / bracket a c) • a := by
  have h1 : bracket a c * b.1 - bracket b c * a.1 = bracket a b * c.1 := by
    unfold bracket
    ring
  have h2 : bracket a c * b.2 - bracket b c * a.2 = bracket a b * c.2 := by
    unfold bracket
    ring
  rw [hab, zero_mul] at h1 h2
  apply Prod.ext
  · change b.1 = (bracket b c / bracket a c) * a.1
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hac).mpr
    rw [mul_comm b.1]
    exact sub_eq_zero.mp h1
  · change b.2 = (bracket b c / bracket a c) * a.2
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hac).mpr
    rw [mul_comm b.2]
    exact sub_eq_zero.mp h2

/-- The fourth projective point is determined by its cross ratio on the
complement of the second point of a nondegenerate reference triple. -/
theorem eq_of_crossRatio_eq (a b c d e : Projectivization K (K × K))
    (hba : bracket b.rep a.rep ≠ 0) (hca : bracket c.rep a.rep ≠ 0)
    (hcb : bracket c.rep b.rep ≠ 0)
    (hdb : bracket d.rep b.rep ≠ 0) (heb : bracket e.rep b.rep ≠ 0)
    (h : crossRatio a b c d = crossRatio a b c e) : d = e := by
  have hde : bracket d.rep e.rep = 0 :=
    bracket_eq_zero_of_homogeneousCrossRatio_eq a.rep b.rep c.rep d.rep e.rep
      hba hca hcb hdb heb h
  have hed : bracket e.rep d.rep = 0 := by rw [bracket_swap, hde, neg_zero]
  have hs := eq_smul_of_bracket_eq_zero e.rep d.rep b.rep heb hed
  have hm := (Projectivization.mk_eq_mk_iff' K d.rep e.rep d.rep_nonzero e.rep_nonzero).mpr
    ⟨bracket d.rep b.rep / bracket e.rep b.rep, hs.symm⟩
  simpa only [Projectivization.mk_rep] using hm

/-- A nonzero homogeneous vector has a nonzero bracket with some vector. -/
theorem exists_bracket_ne_zero (a : K × K) (ha : a ≠ 0) :
    ∃ c : K × K, bracket a c ≠ 0 := by
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := by
      intro h2
      apply ha
      exact Prod.ext h1 h2
    refine ⟨(1, 0), ?_⟩
    simpa only [bracket, mul_zero, mul_one, zero_sub, neg_ne_zero] using h2
  · refine ⟨(0, 1), ?_⟩
    simpa only [bracket, mul_one, mul_zero, sub_zero] using h1

/-- Equality of projective points is exactly vanishing of their representative bracket. -/
theorem bracket_rep_eq_zero_iff (d e : Projectivization K (K × K)) :
    bracket d.rep e.rep = 0 ↔ d = e := by
  constructor
  · intro hde
    obtain ⟨c, hc⟩ := exists_bracket_ne_zero e.rep e.rep_nonzero
    have hed : bracket e.rep d.rep = 0 := by rw [bracket_swap, hde, neg_zero]
    have hs := eq_smul_of_bracket_eq_zero e.rep d.rep c hc hed
    have hm := (Projectivization.mk_eq_mk_iff' K d.rep e.rep d.rep_nonzero e.rep_nonzero).mpr
      ⟨bracket d.rep c / bracket e.rep c, hs.symm⟩
    simpa only [Projectivization.mk_rep] using hm
  · rintro rfl
    unfold bracket
    ring

/-- An intrinsic version of cross-ratio separation, using only inequalities
between projective points rather than conditions on chosen coordinates. -/
theorem eq_of_crossRatio_eq_of_ne (a b c d e : Projectivization K (K × K))
    (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) (hdb : d ≠ b) (heb : e ≠ b)
    (h : crossRatio a b c d = crossRatio a b c e) : d = e := by
  exact eq_of_crossRatio_eq a b c d e
    (fun hz => hba ((bracket_rep_eq_zero_iff b a).mp hz))
    (fun hz => hca ((bracket_rep_eq_zero_iff c a).mp hz))
    (fun hz => hcb ((bracket_rep_eq_zero_iff c b).mp hz))
    (fun hz => hdb ((bracket_rep_eq_zero_iff d b).mp hz))
    (fun hz => heb ((bracket_rep_eq_zero_iff e b).mp hz)) h

end AnabelianGeometry.ProjectiveLine

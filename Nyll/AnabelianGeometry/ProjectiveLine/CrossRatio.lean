/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.Ring

/-!
# Cross ratios on the projective line

The convention sends the first three ordered points to `0, ∞, 1`.
Homogeneous coordinates include infinity without a separate affine chart.
Independent rescaling does not change the ratio, and the projective
definition is evaluated by the proved representative formula.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u

variable {K : Type u} [Field K]

/-- The alternating determinant of two homogeneous coordinates. -/
def bracket (a b : K × K) : K := a.1 * b.2 - a.2 * b.1

/-- The cross ratio in homogeneous coordinates, with convention `(0, ∞, 1, t) ↦ t`.
As with field division, this is a total function; geometric applications use distinct points. -/
def homogeneousCrossRatio (a b c d : K × K) : K :=
  (bracket d a * bracket c b) / (bracket d b * bracket c a)

/-- Determinants multiply by both scalar factors. -/
theorem bracket_smul (a b : K × K) (s t : K) :
    bracket (s • a) (t • b) = (s * t) * bracket a b := by
  change (s * a.1) * (t * b.2) - (s * a.2) * (t * b.1) =
    (s * t) * (a.1 * b.2 - a.2 * b.1)
  ring

/-- Swapping the two coordinates of a determinant changes its sign. -/
theorem bracket_swap (a b : K × K) : bracket a b = -bracket b a := by
  unfold bracket
  ring

/-- Independent nonzero rescaling of the four representatives preserves the cross ratio. -/
theorem homogeneousCrossRatio_smul (a b c d : K × K) (s t u v : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    homogeneousCrossRatio (s • a) (t • b) (u • c) (v • d) =
      homogeneousCrossRatio a b c d := by
  simp only [homogeneousCrossRatio, bracket_smul]
  have hn : s * t * u * v ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hs ht) hu) hv
  rw [show (v * s * bracket d a) * (u * t * bracket c b) =
      (s * t * u * v) * (bracket d a * bracket c b) by ring]
  rw [show (v * t * bracket d b) * (u * s * bracket c a) =
      (s * t * u * v) * (bracket d b * bracket c a) by ring]
  exact mul_div_mul_left _ _ hn

/-- The cross ratio of four points of the projective line. -/
noncomputable def crossRatio (a b c d : Projectivization K (K × K)) : K :=
  homogeneousCrossRatio a.rep b.rep c.rep d.rep

/-- The projective cross ratio can be computed with any nonzero representatives. -/
theorem crossRatio_mk (a b c d : K × K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    crossRatio (Projectivization.mk K a ha) (Projectivization.mk K b hb)
      (Projectivization.mk K c hc) (Projectivization.mk K d hd) =
        homogeneousCrossRatio a b c d := by
  obtain ⟨s, hs⟩ := Projectivization.exists_smul_eq_mk_rep K a ha
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep K b hb
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K c hc
  obtain ⟨v, hv⟩ := Projectivization.exists_smul_eq_mk_rep K d hd
  unfold crossRatio
  rw [← hs, ← ht, ← hu, ← hv]
  change homogeneousCrossRatio ((s : K) • a) ((t : K) • b)
      ((u : K) • c) ((v : K) • d) = homogeneousCrossRatio a b c d
  exact homogeneousCrossRatio_smul a b c d s t u v
    s.ne_zero t.ne_zero u.ne_zero v.ne_zero

/-- Evaluation in the normalized coordinate. -/
theorem homogeneousCrossRatio_zero_infty_one (t : K) :
    homogeneousCrossRatio (0, 1) (1, 0) (1, 1) (t, 1) = t := by
  simp only [homogeneousCrossRatio, bracket, mul_one, mul_zero,
    sub_zero, zero_sub, mul_neg, neg_div_neg_eq, div_one]

/-- Simultaneously swapping the first pair and the last pair preserves the cross ratio. -/
theorem homogeneousCrossRatio_swap_pairs (a b c d : K × K) :
    homogeneousCrossRatio b a d c = homogeneousCrossRatio a b c d := by
  unfold homogeneousCrossRatio
  rw [mul_comm (bracket c b), mul_comm (bracket c a)]

/-- Swapping the first two points inverts the cross ratio, even for degenerate coordinates. -/
theorem homogeneousCrossRatio_swap_first (a b c d : K × K) :
    homogeneousCrossRatio b a c d = (homogeneousCrossRatio a b c d)⁻¹ := by
  simp only [homogeneousCrossRatio, inv_div]

/-- Four appropriate nonzero determinants give a nonzero cross ratio. -/
theorem homogeneousCrossRatio_ne_zero (a b c d : K × K)
    (hda : bracket d a ≠ 0) (hcb : bracket c b ≠ 0)
    (hdb : bracket d b ≠ 0) (hca : bracket c a ≠ 0) :
    homogeneousCrossRatio a b c d ≠ 0 :=
  div_ne_zero (mul_ne_zero hda hcb) (mul_ne_zero hdb hca)

/-- The determinant identity underlying the six cross-ratio transformations. -/
theorem bracket_crossRatio_relation (a b c d : K × K) :
    bracket d b * bracket c a - bracket d a * bracket c b =
      bracket d c * bracket b a := by
  unfold bracket
  ring

/-- The complementary cross ratio is another quotient of the same brackets. -/
theorem one_sub_homogeneousCrossRatio (a b c d : K × K)
    (hdb : bracket d b ≠ 0) (hca : bracket c a ≠ 0) :
    1 - homogeneousCrossRatio a b c d =
      (bracket d c * bracket b a) / (bracket d b * bracket c a) := by
  have hden : bracket d b * bracket c a ≠ 0 := mul_ne_zero hdb hca
  calc
    1 - homogeneousCrossRatio a b c d =
        (bracket d b * bracket c a) / (bracket d b * bracket c a) -
          (bracket d a * bracket c b) / (bracket d b * bracket c a) := by
            rw [div_self hden]
            rfl
    _ = (bracket d c * bracket b a) / (bracket d b * bracket c a) := by
      rw [← sub_div, bracket_crossRatio_relation]

/-- The cross ratio cannot equal one when both pairs are distinct and its denominator is nonzero. -/
theorem homogeneousCrossRatio_ne_one (a b c d : K × K)
    (hdb : bracket d b ≠ 0) (hca : bracket c a ≠ 0)
    (hdc : bracket d c ≠ 0) (hba : bracket b a ≠ 0) :
    homogeneousCrossRatio a b c d ≠ 1 := by
  intro h
  have heq : bracket d a * bracket c b = bracket d b * bracket c a :=
    (div_eq_one_iff_eq (mul_ne_zero hdb hca)).mp h
  have hz : bracket d c * bracket b a = 0 := by
    rw [← bracket_crossRatio_relation, heq, sub_self]
  exact mul_ne_zero hdc hba hz

/-- A linear change of homogeneous coordinates. -/
def transform (α β γ δ : K) (a : K × K) : K × K :=
  (α * a.1 + β * a.2, γ * a.1 + δ * a.2)

/-- A linear change multiplies each bracket by its determinant. -/
theorem bracket_transform (α β γ δ : K) (a b : K × K) :
    bracket (transform α β γ δ a) (transform α β γ δ b) =
      (α * δ - β * γ) * bracket a b := by
  unfold bracket transform
  ring

/-- Every invertible linear coordinate change preserves the homogeneous cross ratio. -/
theorem homogeneousCrossRatio_transform (α β γ δ : K)
    (h : α * δ - β * γ ≠ 0) (a b c d : K × K) :
    homogeneousCrossRatio (transform α β γ δ a) (transform α β γ δ b)
      (transform α β γ δ c) (transform α β γ δ d) =
        homogeneousCrossRatio a b c d := by
  simp only [homogeneousCrossRatio, bracket_transform]
  rw [show ((α * δ - β * γ) * bracket d a) *
      ((α * δ - β * γ) * bracket c b) =
      ((α * δ - β * γ) * (α * δ - β * γ)) *
        (bracket d a * bracket c b) by ring]
  rw [show ((α * δ - β * γ) * bracket d b) *
      ((α * δ - β * γ) * bracket c a) =
      ((α * δ - β * γ) * (α * δ - β * γ)) *
        (bracket d b * bracket c a) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero h h)

end AnabelianGeometry.ProjectiveLine

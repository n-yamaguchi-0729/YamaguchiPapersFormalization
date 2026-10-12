/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

/-!
# Determinants of integral homogeneous coordinates

The determinant of two primitive integral coordinate pairs controls the intersection
of their rational sections. This file proves its change-of-coordinates identities.
The scheme-theoretic intersection multiplicity comparison is a separate result.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Lemma 2.3.
-/

namespace ShimizuYamaguchi26BranchedCoverings

/-- The signed determinant of two integral homogeneous coordinate pairs. -/
def coordinateDeterminant (u v u' v' : ℤ) : ℤ := u * v' - v * u'

/-- Swapping the two coordinate pairs reverses the determinant's sign. -/
theorem coordinateDeterminant_swap (u v u' v' : ℤ) :
    coordinateDeterminant u' v' u v = -coordinateDeterminant u v u' v' := by
  unfold coordinateDeterminant
  ring

/-- An integral change of coordinates multiplies the determinant by the
matrix determinant. -/
theorem coordinateDeterminant_transform (a b c d u v u' v' : ℤ) :
    coordinateDeterminant (a * u + b * v) (c * u + d * v)
      (a * u' + b * v') (c * u' + d * v') =
        (a * d - b * c) * coordinateDeterminant u v u' v' := by
  unfold coordinateDeterminant
  ring

/-- Divisibility of the determinant is unchanged by an integral matrix of
determinant `1` or `-1`. In particular this applies to every prime power. -/
theorem dvd_coordinateDeterminant_transform_iff
    (a b c d u v u' v' m : ℤ) (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1) :
    m ∣ coordinateDeterminant (a * u + b * v) (c * u + d * v)
      (a * u' + b * v') (c * u' + d * v') ↔
        m ∣ coordinateDeterminant u v u' v' := by
  rw [coordinateDeterminant_transform]
  rcases hdet with hdet | hdet
  · rw [hdet, one_mul]
  · rw [hdet, neg_one_mul]
    exact Int.dvd_neg

/-- Bezout coefficients give the integral coordinate change used to move a
primitive section to infinity. Its second row is `(v,-u)`. -/
theorem exists_integral_change_sending_to_infinity
    (u v : ℤ) (huv : IsCoprime u v) :
    ∃ a b : ℤ, a * u + b * v = 1 ∧
      coordinateDeterminant a b v (-u) = -1 := by
  obtain ⟨a, b, hab⟩ := huv
  refine ⟨a, b, hab, ?_⟩
  calc
    coordinateDeterminant a b v (-u) = -(a * u + b * v) := by
      unfold coordinateDeterminant
      ring
    _ = -1 := congrArg Neg.neg hab

/-- The normalized coordinates of a second primitive pair remain primitive
under the explicit integral change sending the first pair to infinity.
The witnesses are computed from the original two Bezout identities. -/
theorem isCoprime_normalizedCoordinates
    (u v a b u' v' : ℤ) (hab : a * u + b * v = 1)
    (huv' : IsCoprime u' v') :
    IsCoprime (-(a * u' + b * v')) (coordinateDeterminant u v u' v') := by
  obtain ⟨c, d, hcd⟩ := huv'
  refine ⟨-(c * u + d * v), -c * b + d * a, ?_⟩
  calc
    _ = (a * u + b * v) * (c * u' + d * v') := by
      unfold coordinateDeterminant
      ring
    _ = 1 := by rw [hab, hcd, one_mul]

end ShimizuYamaguchi26BranchedCoverings

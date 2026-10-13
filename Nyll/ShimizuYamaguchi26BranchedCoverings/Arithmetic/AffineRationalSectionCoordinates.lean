/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.Normalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Primitive coordinates of explicit affine rational points

These computations use the existing affine and infinity points. The quotient's
chosen representative need not be the displayed vector: its nonzero scalar
is obtained from `Projectivization.exists_smul_eq_mk_rep` and cancels in the
affine ratio. Thus the existing canonical numerator, denominator, and paper
Delta can be evaluated without assuming any particular quotient choice.
-/

noncomputable section

open AnabelianGeometry.ProjectiveLine

namespace ShimizuYamaguchi26BranchedCoverings

private lemma affinePoint_rep_coordinates (q : ℚ) :
    (affinePoint q).rep.2 ≠ 0 ∧ (affinePoint q).rep.1 / (affinePoint q).rep.2 = q := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℚ
    (q, (1 : ℚ)) (fun h => one_ne_zero (congrArg Prod.snd h))
  have hrep : (affinePoint q).rep = ((c : ℚ) * q, (c : ℚ)) := by
    change ((c : ℚ) * q, (c : ℚ) * 1) = (affinePoint q).rep at hc
    exact hc.symm.trans (congrArg (fun z : ℚ => ((c : ℚ) * q, z)) (mul_one (c : ℚ)))
  rw [hrep]
  exact ⟨c.ne_zero, mul_div_cancel_left₀ q c.ne_zero⟩

private lemma infinityPoint_rep_snd : (infinityPoint (K := ℚ)).rep.2 = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℚ
    ((1 : ℚ), (0 : ℚ)) (fun h => one_ne_zero (congrArg Prod.fst h))
  have h := congrArg Prod.snd hc
  change (c : ℚ) * 0 = (infinityPoint (K := ℚ)).rep.2 at h
  exact h.symm.trans (mul_zero (c : ℚ))

/-- The canonical coordinates of an affine rational point are its reduced
numerator and denominator, independently of the chosen homogeneous representative. -/
theorem rationalPointCoordinates_affine (q : ℚ) :
    rationalPointNumerator (affinePoint q) = q.num ∧
      rationalPointDenominator (affinePoint q) = (q.den : ℤ) := by
  obtain ⟨hsecond, hratio⟩ := affinePoint_rep_coordinates q
  constructor
  · rw [rationalPointNumerator, ite_eq_right hsecond, hratio]
  · rw [rationalPointDenominator, ite_eq_right hsecond, hratio]

/-- An integral affine point has exactly the primitive coordinates `(n,1)`. -/
theorem rationalPointCoordinates_affine_int (n : ℤ) :
    rationalPointNumerator (affinePoint (n : ℚ)) = n ∧
      rationalPointDenominator (affinePoint (n : ℚ)) = 1 := by
  simpa only [Rat.num_intCast, Rat.den_intCast, Nat.cast_one] using
    rationalPointCoordinates_affine (n : ℚ)

/-- The canonical primitive coordinates of the existing point at infinity. -/
theorem rationalPointCoordinates_infinity :
    rationalPointNumerator (infinityPoint (K := ℚ)) = 1 ∧
      rationalPointDenominator (infinityPoint (K := ℚ)) = 0 := by
  constructor
  · rw [rationalPointNumerator, ite_eq_left infinityPoint_rep_snd]
  · rw [rationalPointDenominator, ite_eq_left infinityPoint_rep_snd]

/-- The paper's Delta for two integral affine points is their difference. -/
theorem rationalPointDelta_affine_int (m n : ℤ) :
    rationalPointDelta (affinePoint (m : ℚ)) (affinePoint (n : ℚ)) = m - n := by
  rw [rationalPointDelta, ite_eq_right (affinePoint_rep_coordinates (n : ℚ)).1,
    ite_eq_right (affinePoint_rep_coordinates (m : ℚ)).1, coordinateDeterminant,
    (rationalPointCoordinates_affine_int m).1, (rationalPointCoordinates_affine_int m).2,
    (rationalPointCoordinates_affine_int n).1, (rationalPointCoordinates_affine_int n).2,
    mul_one, one_mul]

/-- A finite integral section and infinity have determinant one in the paper's
unsigned-at-infinity convention. -/
theorem rationalPointDelta_affine_int_infinity (n : ℤ) :
    rationalPointDelta (affinePoint (n : ℚ)) (infinityPoint (K := ℚ)) = 1 := by
  rw [rationalPointDelta, ite_eq_left infinityPoint_rep_snd]
  exact (rationalPointCoordinates_affine_int n).2

/-- The same determinant-one computation in the opposite order. -/
theorem rationalPointDelta_infinity_affine_int (n : ℤ) :
    rationalPointDelta (infinityPoint (K := ℚ)) (affinePoint (n : ℚ)) = 1 := by
  rw [rationalPointDelta, ite_eq_right (affinePoint_rep_coordinates (n : ℚ)).1,
    ite_eq_left infinityPoint_rep_snd]
  exact (rationalPointCoordinates_affine_int n).2

end ShimizuYamaguchi26BranchedCoverings

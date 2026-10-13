/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.CrossRatio
import Nyll.AnabelianGeometry.ProjectiveLine.CrossRatioSeparation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Rat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-!
# Primitive integer coordinates of rational projective points

For an actual point of `Projectivization ℚ (ℚ × ℚ)`, the coordinates are
`(1, 0)` at infinity and the reduced numerator and positive denominator of
the affine coordinate elsewhere. Their primitivity and their representation
of the original projective point are proved from these formulas. Distinct
points consequently have nonzero integral coordinate determinant.

The paper's `Δ` uses a positive denominator when either point is infinity.
It therefore differs from the signed coordinate determinant by a minus sign
when the second point is infinity. This sign does not change `padicValInt`.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
the coordinate convention preceding Lemma 2.3 and its use in Lemma 2.4.
-/

noncomputable section

namespace ShimizuYamaguchi26BranchedCoverings

open AnabelianGeometry.ProjectiveLine

/-- The primitive numerator of a rational projective point, equal to `1` at infinity. -/
def rationalPointNumerator (a : Projectivization ℚ (ℚ × ℚ)) : ℤ :=
  if a.rep.2 = 0 then 1 else (a.rep.1 / a.rep.2).num

/-- The primitive denominator, equal to `0` at infinity and positive otherwise. -/
def rationalPointDenominator (a : Projectivization ℚ (ℚ × ℚ)) : ℤ :=
  if a.rep.2 = 0 then 0 else ((a.rep.1 / a.rep.2).den : ℤ)

/-- The rational homogeneous vector obtained from the primitive integer coordinates. -/
def rationalPointCoordinates (a : Projectivization ℚ (ℚ × ℚ)) : ℚ × ℚ :=
  ((rationalPointNumerator a : ℚ), (rationalPointDenominator a : ℚ))

/-- The coordinates constructed from the point are primitive over the integers. -/
theorem rationalPointCoordinates_isCoprime (a : Projectivization ℚ (ℚ × ℚ)) :
    IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) := by
  by_cases h : a.rep.2 = 0
  · simp only [rationalPointNumerator, rationalPointDenominator, ite_eq_left h]
    exact isCoprime_one_left
  · simp only [rationalPointNumerator, rationalPointDenominator, ite_eq_right h]
    exact Rat.isCoprime_num_den (a.rep.1 / a.rep.2)

private theorem exists_smul_rationalPointCoordinates_eq_rep
    (a : Projectivization ℚ (ℚ × ℚ)) :
    ∃ c : ℚ, c • rationalPointCoordinates a = a.rep := by
  by_cases h : a.rep.2 = 0
  · have hc : rationalPointCoordinates a = (1, 0) := by
      simp only [rationalPointCoordinates, rationalPointNumerator,
        rationalPointDenominator, ite_eq_left h, Int.cast_one, Int.cast_zero]
    refine ⟨a.rep.1, ?_⟩
    rw [hc]
    apply Prod.ext
    · change a.rep.1 * 1 = a.rep.1
      exact mul_one _
    · change a.rep.1 * 0 = a.rep.2
      rw [mul_zero, h]
  · let q : ℚ := a.rep.1 / a.rep.2
    have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    have hc : rationalPointCoordinates a = ((q.num : ℚ), (q.den : ℚ)) := by
      simp only [rationalPointCoordinates, rationalPointNumerator,
        rationalPointDenominator, ite_eq_right h, Int.cast_natCast, q]
    refine ⟨a.rep.2 / (q.den : ℚ), ?_⟩
    rw [hc]
    apply Prod.ext
    · change (a.rep.2 / (q.den : ℚ)) * (q.num : ℚ) = a.rep.1
      calc
        (a.rep.2 / (q.den : ℚ)) * (q.num : ℚ) =
            a.rep.2 * ((q.num : ℚ) / (q.den : ℚ)) := by ring
        _ = a.rep.2 * q := by rw [Rat.num_div_den]
        _ = a.rep.1 := mul_div_cancel₀ a.rep.1 h
    · change (a.rep.2 / (q.den : ℚ)) * (q.den : ℚ) = a.rep.2
      exact div_mul_cancel₀ a.rep.2 hd

/-- The primitive homogeneous vector is nonzero. -/
theorem rationalPointCoordinates_ne_zero (a : Projectivization ℚ (ℚ × ℚ)) :
    rationalPointCoordinates a ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := exists_smul_rationalPointCoordinates_eq_rep a
  apply a.rep_nonzero
  rw [← hc, hz, smul_zero]

/-- The constructed integer coordinates represent the original projective point. -/
theorem rationalPointCoordinates_mk (a : Projectivization ℚ (ℚ × ℚ)) :
    Projectivization.mk ℚ (rationalPointCoordinates a)
      (rationalPointCoordinates_ne_zero a) = a := by
  obtain ⟨c, hc⟩ := exists_smul_rationalPointCoordinates_eq_rep a
  have hm : Projectivization.mk ℚ a.rep a.rep_nonzero =
      Projectivization.mk ℚ (rationalPointCoordinates a)
        (rationalPointCoordinates_ne_zero a) :=
    (Projectivization.mk_eq_mk_iff' ℚ a.rep (rationalPointCoordinates a)
      a.rep_nonzero (rationalPointCoordinates_ne_zero a)).mpr ⟨c, hc⟩
  exact hm.symm.trans (Projectivization.mk_rep a)

/-- Different rational projective points have nonzero primitive coordinate determinant. -/
theorem rationalPoint_coordinateDeterminant_ne_zero
    (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b) :
    coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
      (rationalPointNumerator b) (rationalPointDenominator b) ≠ 0 := by
  intro hz
  have hbr : bracket (rationalPointCoordinates a) (rationalPointCoordinates b) = 0 := by
    have hcast := congrArg (fun z : ℤ => (z : ℚ)) hz
    simpa only [coordinateDeterminant, Int.cast_sub, Int.cast_mul, Int.cast_zero,
      rationalPointCoordinates, bracket] using hcast
  obtain ⟨c, hc⟩ := exists_smul_rationalPointCoordinates_eq_rep a
  obtain ⟨d, hd⟩ := exists_smul_rationalPointCoordinates_eq_rep b
  apply hab
  apply (bracket_rep_eq_zero_iff a b).mp
  rw [← hc, ← hd, bracket_smul, hbr, mul_zero]

/-- The integer `Δ(a,b)` used in the paper, with value `0` when both points are infinity. -/
def rationalPointDelta (a b : Projectivization ℚ (ℚ × ℚ)) : ℤ :=
  if b.rep.2 = 0 then rationalPointDenominator a
  else if a.rep.2 = 0 then rationalPointDenominator b
  else coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
    (rationalPointNumerator b) (rationalPointDenominator b)

/-- The exact sign comparison between the paper's `Δ` and the homogeneous determinant. -/
theorem rationalPointDelta_eq_signed_coordinateDeterminant
    (a b : Projectivization ℚ (ℚ × ℚ)) :
    rationalPointDelta a b =
      if b.rep.2 = 0 then
        -coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
          (rationalPointNumerator b) (rationalPointDenominator b)
      else coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
        (rationalPointNumerator b) (rationalPointDenominator b) := by
  by_cases hb : b.rep.2 = 0
  · simp only [rationalPointDelta, coordinateDeterminant,
      rationalPointNumerator, rationalPointDenominator, ite_eq_left hb,
      mul_zero, mul_one, zero_sub, neg_neg]
  · by_cases ha : a.rep.2 = 0
    · simp only [rationalPointDelta, coordinateDeterminant,
        rationalPointNumerator, rationalPointDenominator, ite_eq_left ha, ite_eq_right hb,
        one_mul, zero_mul, sub_zero]
    · simp only [rationalPointDelta, ite_eq_right hb, ite_eq_right ha]

/-- Divisibility of the paper's integer agrees with divisibility of the signed
homogeneous determinant, including either point at infinity. -/
theorem rationalPointDelta_dvd_iff (p : ℕ)
    (a b : Projectivization ℚ (ℚ × ℚ)) :
    (p : ℤ) ∣ rationalPointDelta a b ↔
      (p : ℤ) ∣ coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
        (rationalPointNumerator b) (rationalPointDenominator b) := by
  rw [rationalPointDelta_eq_signed_coordinateDeterminant]
  by_cases hb : b.rep.2 = 0
  · rw [ite_eq_left hb]
    exact Int.dvd_neg
  · rw [ite_eq_right hb]

/-- The extended determinant vanishes when both rational points coincide. -/
theorem rationalPointDelta_self (a : Projectivization ℚ (ℚ × ℚ)) :
    rationalPointDelta a a = 0 := by
  rw [rationalPointDelta_eq_signed_coordinateDeterminant]
  simp only [coordinateDeterminant, mul_comm, sub_self, neg_zero, ite_self]

/-- The paper's integer and the coordinate determinant have the same value at every prime. -/
theorem padicValInt_rationalPointDelta (p : ℕ)
    (a b : Projectivization ℚ (ℚ × ℚ)) :
    padicValInt p (rationalPointDelta a b) =
      padicValInt p (coordinateDeterminant (rationalPointNumerator a)
        (rationalPointDenominator a) (rationalPointNumerator b)
        (rationalPointDenominator b)) := by
  rw [rationalPointDelta_eq_signed_coordinateDeterminant]
  by_cases hb : b.rep.2 = 0
  · simp only [ite_eq_left hb, padicValInt, Int.natAbs_neg]
  · rw [ite_eq_right hb]

end ShimizuYamaguchi26BranchedCoverings

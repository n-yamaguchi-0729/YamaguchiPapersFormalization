/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPointUniqueness
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic.Ring

/-!
# Rational section intersections in a prime special fibre

A common point of two homogeneous linear equations over a field forces the
coordinate determinant to vanish: two explicit linear combinations put the
determinant times both coordinates in its homogeneous prime ideal, and an
invertible determinant would put the irrelevant ideal there.

Conversely, the homogeneous core of evaluation at the reduction of the first
primitive pair constructs the intersection point. Its evaluation formula
identifies meeting with divisibility of the integer determinant, with the
paper's sign convention at infinity. The zero locus of either individual
section in the special fibre is a singleton closed point.

These are the incidence and unique-closed-point assertions of Lemma 2.3 of
Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The local intersection-length and normal-crossing assertions of that lemma
are separate requirements.
-/

noncomputable section

open AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A common point of two linear equations over a field forces their determinant to vanish. -/
theorem determinant_eq_zero_of_common_field_section_point
    {k : Type u} [Field k] (u v s t : k) (x : ProjectiveLine k)
    (hfirst : linearSectionEquation u v ∈ x.asHomogeneousIdeal)
    (hsecond : linearSectionEquation s t ∈ x.asHomogeneousIdeal) : u * t - v * s = 0 := by
  by_contra hdet
  have hzero : MvPolynomial.C (u * t - v * s) * MvPolynomial.X (0 : Fin 2) ∈
      x.asHomogeneousIdeal.toIdeal := by
    have heq : MvPolynomial.C (u * t - v * s) * MvPolynomial.X (0 : Fin 2) =
        MvPolynomial.C u * linearSectionEquation s t -
          MvPolynomial.C s * linearSectionEquation u v := by
      simp only [linearSectionEquation, map_sub, map_mul]
      ring
    rw [heq]
    exact x.asHomogeneousIdeal.toIdeal.sub_mem
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C u) hsecond)
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C s) hfirst)
  have hone : MvPolynomial.C (u * t - v * s) * MvPolynomial.X (1 : Fin 2) ∈
      x.asHomogeneousIdeal.toIdeal := by
    have heq : MvPolynomial.C (u * t - v * s) * MvPolynomial.X (1 : Fin 2) =
        MvPolynomial.C v * linearSectionEquation s t -
          MvPolynomial.C t * linearSectionEquation u v := by
      simp only [linearSectionEquation, map_sub, map_mul]
      ring
    rw [heq]
    exact x.asHomogeneousIdeal.toIdeal.sub_mem
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C v) hsecond)
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C t) hfirst)
  have hcancel : ∀ i : Fin 2,
      MvPolynomial.C (u * t - v * s) * MvPolynomial.X i ∈ x.asHomogeneousIdeal.toIdeal →
        MvPolynomial.X i ∈ x.asHomogeneousIdeal.toIdeal := by
    intro i hi
    have hmul := x.asHomogeneousIdeal.toIdeal.mul_mem_left
      (MvPolynomial.C ((u * t - v * s)⁻¹)) hi
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hdet, map_one, one_mul] at hmul
    exact hmul
  exact projectiveLine_not_both_coordinates_mem x (hcancel 0 hzero) (hcancel 1 hone)

private theorem reduced_rationalPointCoordinates_ne_zero (p : ℕ) [Fact p.Prime]
    (a : Projectivization ℚ (ℚ × ℚ)) :
    (rationalPointNumerator a : ZMod p) ≠ 0 ∨ (rationalPointDenominator a : ZMod p) ≠ 0 :=
  ((rationalPointCoordinates_isCoprime a).intCast (R := ZMod p)).ne_zero_or_ne_zero

/-- The actual point of the prime special fibre selected by a rational section. -/
def rationalSectionSpecialFiberPoint (p : ℕ) [Fact p.Prime]
    (a : Projectivization ℚ (ℚ × ℚ)) : ProjectiveLine (ZMod p) :=
  fieldSectionPoint (rationalPointNumerator a : ZMod p) (rationalPointDenominator a : ZMod p)
    (reduced_rationalPointCoordinates_ne_zero p a)

private theorem prime_dvd_delta_iff (p : ℕ)
    (a b : Projectivization ℚ (ℚ × ℚ)) :
    (p : ℤ) ∣ rationalPointDelta a b ↔
      (p : ℤ) ∣ coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
        (rationalPointNumerator b) (rationalPointDenominator b) := by
  rw [rationalPointDelta_eq_signed_coordinateDeterminant]
  by_cases hb : b.rep.2 = 0
  · rw [ite_eq_left hb]
    exact Int.dvd_neg
  · rw [ite_eq_right hb]

/-- The reduction point of the first section belongs to the second section
exactly when the prime divides the paper's integer `Δ`. -/
theorem rationalSectionSpecialFiberPoint_mem_iff (p : ℕ) [Fact p.Prime]
    (a b : Projectivization ℚ (ℚ × ℚ)) :
    (ProjSpace.map ℤ (ZMod p) 1) (rationalSectionSpecialFiberPoint p a) ∈
        rationalSectionSupport b ↔ (p : ℤ) ∣ rationalPointDelta a b := by
  rw [mem_rationalSectionSupport_baseChange_iff]
  unfold rationalSectionSpecialFiberPoint
  rw [linearSectionEquation_mem_fieldSectionPoint_iff, prime_dvd_delta_iff,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [coordinateDeterminant, Int.cast_sub, Int.cast_mul,
    mul_comm (rationalPointDenominator b : ZMod p) (rationalPointNumerator a : ZMod p),
    mul_comm (rationalPointNumerator b : ZMod p) (rationalPointDenominator a : ZMod p)]

/-- The constructed reduction point lies on its original rational section. -/
theorem rationalSectionSpecialFiberPoint_mem (p : ℕ) [Fact p.Prime]
    (a : Projectivization ℚ (ℚ × ℚ)) :
    (ProjSpace.map ℤ (ZMod p) 1) (rationalSectionSpecialFiberPoint p a) ∈
      rationalSectionSupport a := by
  rw [mem_rationalSectionSupport_baseChange_iff]
  exact linearSectionEquation_mem_fieldSectionPoint _ _
    (reduced_rationalPointCoordinates_ne_zero p a)

/-- The incidence assertion of Lemma 2.3: the two actual integral section
supports meet in the prime special fibre if and only if the prime divides `Δ`.
This holds also for equal rational points, where both sides hold. -/
theorem specialFiber_intersection_nonempty_iff (p : ℕ) [Fact p.Prime]
    (a b : Projectivization ℚ (ℚ × ℚ)) :
    (∃ x : ProjectiveLine (ZMod p), (ProjSpace.map ℤ (ZMod p) 1) x ∈ rationalSectionSupport a ∧
      (ProjSpace.map ℤ (ZMod p) 1) x ∈ rationalSectionSupport b) ↔
        (p : ℤ) ∣ rationalPointDelta a b := by
  constructor
  · rintro ⟨x, ha, hb⟩
    have hdet := determinant_eq_zero_of_common_field_section_point
      (rationalPointNumerator a : ZMod p) (rationalPointDenominator a : ZMod p)
      (rationalPointNumerator b : ZMod p) (rationalPointDenominator b : ZMod p) x
      ((mem_rationalSectionSupport_baseChange_iff (ZMod p) a x).mp ha)
      ((mem_rationalSectionSupport_baseChange_iff (ZMod p) b x).mp hb)
    apply (prime_dvd_delta_iff p a b).mpr
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [coordinateDeterminant, Int.cast_sub, Int.cast_mul] using hdet
  · intro hdiv
    exact ⟨rationalSectionSpecialFiberPoint p a, rationalSectionSpecialFiberPoint_mem p a,
      (rationalSectionSpecialFiberPoint_mem_iff p a b).mpr hdiv⟩

/-- When the prime divides `Δ`, the entire intersection in the actual special
fibre is the singleton constructed from the first section, and this point is closed.
This is the unique-closed-point assertion of Lemma 2.3. -/
theorem specialFiber_intersection_singleton_closed (p : ℕ) [Fact p.Prime]
    (a b : Projectivization ℚ (ℚ × ℚ)) (hdiv : (p : ℤ) ∣ rationalPointDelta a b) :
    {x : ProjectiveLine (ZMod p) |
      (ProjSpace.map ℤ (ZMod p) 1) x ∈ rationalSectionSupport a ∧
        (ProjSpace.map ℤ (ZMod p) 1) x ∈ rationalSectionSupport b} =
      {rationalSectionSpecialFiberPoint p a} ∧
        IsClosed ({rationalSectionSpecialFiberPoint p a} : Set (ProjectiveLine (ZMod p))) := by
  constructor
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact eq_fieldSectionPoint_of_linearSection_mem
        (rationalPointNumerator a : ZMod p) (rationalPointDenominator a : ZMod p)
        (reduced_rationalPointCoordinates_ne_zero p a) x
        ((mem_rationalSectionSupport_baseChange_iff (ZMod p) a x).mp hx.1)
    · rintro rfl
      exact ⟨rationalSectionSpecialFiberPoint_mem p a,
        (rationalSectionSpecialFiberPoint_mem_iff p a b).mpr hdiv⟩
  · exact isClosed_singleton_fieldSectionPoint _ _
      (reduced_rationalPointCoordinates_ne_zero p a)

end ShimizuYamaguchi26BranchedCoverings

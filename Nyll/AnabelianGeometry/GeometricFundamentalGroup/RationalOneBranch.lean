/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import Nyll.AlgebraicCurves.Places.Place_inertiaDeg_eq_one_of_isRational
import Nyll.AlgebraicCurves.Places.Place_isRational_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Place_exists_restrict_eq
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Rational covers with at most one tame branch point

Riemann--Hurwitz and the fundamental identity of a place show that a finite separable
extension of an algebraically closed rational function field, tame everywhere and unramified
away from one place, has degree one. In characteristic zero the tameness hypothesis is automatic.

This is a function-field step towards the structure of the fundamental groups of the projective
and affine lines. The scheme-theoretic comparison with finite etale covers is a separate step.
The proof uses the proved Riemann--Hurwitz theorem and does not import the unproved surface
presentation theorem.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F]
  [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]

/-- A tame cover of the rational function field with at most one branch place has degree one. -/
theorem finrank_eq_one_of_tame_one_branch [Algebra.IsSeparable (RatFunc K) F]
    (v : Place K (RatFunc K))
    (htame : ∀ w : Place K F, (w.ramificationIndex (RatFunc K) : K) ≠ 0)
    (hunramified : ∀ w : Place K F, w.restrict (RatFunc K) ≠ v →
      w.ramificationIndex (RatFunc K) = 1) :
    Module.finrank (RatFunc K) F = 1 := by
  classical
  have hsum : ∑ w ∈ v.fiberOver F, (w.ramificationIndex (RatFunc K) : ℤ) =
      (Module.finrank (RatFunc K) F : ℤ) := by
    have hfund := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F) v
    have hterm : ∀ w : Place K F, w.inertiaDeg (RatFunc K) = 1 := by
      intro w
      exact w.inertiaDeg_eq_one_of_isRational (w.isRational_of_isAlgClosed)
        ((w.restrict (RatFunc K)).isRational_of_isAlgClosed)
    simp only [hterm, Nat.cast_one, mul_one] at hfund
    exact hfund
  have hsupport : Function.support (fun w : Place K F =>
      (w.ramificationIndex (RatFunc K) : ℤ) - 1) ⊆ (v.fiberOver F : Set (Place K F)) := by
    intro w hw
    by_contra hnot
    have hne : w.restrict (RatFunc K) ≠ v := fun h => hnot ((Place.mem_fiberOver v).2 h)
    have hzero : (w.ramificationIndex (RatFunc K) : ℤ) - 1 = 0 := by
      rw [hunramified w hne, Nat.cast_one, sub_self]
    exact hw hzero
  have hRH := finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame (K := K) (F := F) htame
  rw [finsum_eq_sum_of_support_subset _ hsupport, Finset.sum_sub_distrib, hsum,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hRH
  obtain ⟨w, hw⟩ := v.exists_restrict_eq (M := F)
  have hcard : 0 < (v.fiberOver F).card :=
    Finset.card_pos.mpr ⟨w, (Place.mem_fiberOver v).2 hw⟩
  have hdegree : 0 < Module.finrank (RatFunc K) F := Module.finrank_pos
  have hgenus : (0 : ℤ) ≤ (genusFF K F : ℤ) := Int.natCast_nonneg _
  omega

/-- In characteristic zero, a rational function-field cover ramified over at most one place
is the original field: the given algebra map is bijective. -/
theorem bijective_algebraMap_of_one_branch [CharZero K] (v : Place K (RatFunc K))
    (hunramified : ∀ w : Place K F, w.restrict (RatFunc K) ≠ v →
      w.ramificationIndex (RatFunc K) = 1) :
    Function.Bijective (algebraMap (RatFunc K) F) := by
  have htame : ∀ w : Place K F, (w.ramificationIndex (RatFunc K) : K) ≠ 0 := by
    intro w
    exact Nat.cast_ne_zero.mpr (w.ramificationIndex_pos (F := RatFunc K)).ne'
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
    (finrank_eq_one_of_tame_one_branch v htame hunramified)

end AnabelianGeometry.GeometricFundamentalGroup

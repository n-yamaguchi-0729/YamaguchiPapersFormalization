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

/-!
# Tame rational covers with at most two branch places

A finite separable extension of an algebraically closed rational function field, tame everywhere
and unramified away from two distinct places, has genus zero and exactly one place above each of
the two possible branch places. This is proved directly from Riemann--Hurwitz and the two local
fundamental identities. It is the ramification step towards classifying covers of the punctured
affine line; a Kummer description and the geometric fundamental-group comparison are separate.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F]
  [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

/-- With at most two tame branch places, the cover has genus zero and a singleton fibre over
each possible branch place. -/
theorem genus_and_fibres_of_tame_two_branches
    (v₀ v₁ : Place K (RatFunc K)) (hne : v₀ ≠ v₁)
    (htame : ∀ w : Place K F, (w.ramificationIndex (RatFunc K) : K) ≠ 0)
    (hunramified : ∀ w : Place K F, w.restrict (RatFunc K) ≠ v₀ →
      w.restrict (RatFunc K) ≠ v₁ → w.ramificationIndex (RatFunc K) = 1) :
    genusFF K F = 0 ∧ (v₀.fiberOver F).card = 1 ∧ (v₁.fiberOver F).card = 1 := by
  classical
  have hsum : ∀ v : Place K (RatFunc K),
      ∑ w ∈ v.fiberOver F, (w.ramificationIndex (RatFunc K) : ℤ) =
        (Module.finrank (RatFunc K) F : ℤ) := by
    intro v
    have hfund := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F) v
    have hterm : ∀ w : Place K F, w.inertiaDeg (RatFunc K) = 1 := by
      intro w
      exact w.inertiaDeg_eq_one_of_isRational (w.isRational_of_isAlgClosed)
        ((w.restrict (RatFunc K)).isRational_of_isAlgClosed)
    simp only [hterm, Nat.cast_one, mul_one] at hfund
    exact hfund
  have hdisjoint : Disjoint (v₀.fiberOver F) (v₁.fiberOver F) := by
    refine Finset.disjoint_left.mpr fun w h₀ h₁ => ?_
    exact hne (((Place.mem_fiberOver v₀).1 h₀).symm.trans
      ((Place.mem_fiberOver v₁).1 h₁))
  have hsupport : Function.support (fun w : Place K F =>
      (w.ramificationIndex (RatFunc K) : ℤ) - 1) ⊆
        (v₀.fiberOver F ∪ v₁.fiberOver F : Finset (Place K F)) := by
    intro w hw
    by_contra hnot
    have h₀ : w.restrict (RatFunc K) ≠ v₀ := fun h =>
      hnot (Finset.mem_union_left _ ((Place.mem_fiberOver v₀).2 h))
    have h₁ : w.restrict (RatFunc K) ≠ v₁ := fun h =>
      hnot (Finset.mem_union_right _ ((Place.mem_fiberOver v₁).2 h))
    have hzero : (w.ramificationIndex (RatFunc K) : ℤ) - 1 = 0 := by
      rw [hunramified w h₀ h₁, Nat.cast_one, sub_self]
    exact hw hzero
  have hRH := finsum_ramificationIndex_ratFunc_sub_one_eq_of_tame (K := K) (F := F) htame
  rw [finsum_eq_sum_of_support_subset _ hsupport, Finset.sum_union hdisjoint,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum v₀, hsum v₁] at hRH
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hRH
  have hcard : ∀ v : Place K (RatFunc K), 0 < (v.fiberOver F).card := by
    intro v
    obtain ⟨w, hw⟩ := v.exists_restrict_eq (M := F)
    exact Finset.card_pos.mpr ⟨w, (Place.mem_fiberOver v).2 hw⟩
  have h₀ := hcard v₀
  have h₁ := hcard v₁
  have hgenus : (0 : ℤ) ≤ (genusFF K F : ℤ) := Int.natCast_nonneg _
  omega

end AnabelianGeometry.GeometricFundamentalGroup

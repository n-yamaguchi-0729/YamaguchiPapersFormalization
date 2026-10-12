/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroParameter
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalTwoBranches
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_isAlgClosed_of_transcendental
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusFF_ratFunc_eq_zero_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Place_ord_algebraMap

/-!
# Power coordinates for rational covers with two branch places

The tame two-branch theorem supplies genus zero and the two singleton fibres. The genus-zero
parameter theorem then supplies actual generating coordinates on both fields. Comparing their
divisors makes the pulled-back base parameter a scalar times a power; an algebraic root of that
scalar absorbs it into the source coordinate. This is a function-field classification, without
using a presentation of an etale fundamental group.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

private theorem curve_of_finite_ratFunc
    {K F : Type} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] : IsCurveOver K F ∧ Algebra.EssFiniteType K F := by
  let x : F := algebraMap (RatFunc K) F RatFunc.X
  have hx : Transcendental K x :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc K) F).injective).mpr
      (RatFunc.transcendental_X (K := K))
  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) :=
    RatFunc.algEquivOfTranscendental x hx
  have hcomm : ∀ r : RatFunc K,
      algebraMap (IntermediateField.adjoin K ({x} : Set F)) F (e r) =
        algebraMap (RatFunc K) F r := by
    intro r
    change (e r : F) = _
    rw [RatFunc.algEquivOfTranscendental_apply]
    have hp : ∀ p : Polynomial K,
        Polynomial.aeval x p = algebraMap (RatFunc K) F (algebraMap (Polynomial K) _ p) := by
      intro p
      exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K (RatFunc K) F)
        RatFunc.X p).trans (congrArg (algebraMap (RatFunc K) F)
          (RatFunc.aeval_X_left_eq_algebraMap p))
    rw [hp, hp, ← map_div₀, RatFunc.num_div_denom]
  have hfinite : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F) (by
      ext r
      exact hcomm r)
  exact ⟨isCurveOver_of_isAlgClosed_of_transcendental x hx,
    essFiniteType_of_transcendental_of_finiteDimensional hx hfinite⟩

open Classical in
private theorem power_parameter
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hg : genusFF K F = 0) (v₀ v₁ : Place K F) (hne : v₀ ≠ v₁)
    (x : F) (hx : x ≠ 0) (n : ℕ) (hn : 0 < n)
    (hord : ∀ v : Place K F, v.ord x =
      (n : ℤ) * ((if v = v₀ then 1 else 0) - (if v = v₁ then 1 else 0))) :
    ∃ t : F, IntermediateField.adjoin K ({t} : Set F) = ⊤ ∧ t ^ n = x := by
  obtain ⟨t, ht, htr, hgen, htord⟩ := exists_parameter_of_genus_zero hg v₀ v₁ hne
  have hfinite : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType htr
  have hquot : ∀ v : Place K F, v.ord (x / t ^ n) = 0 := by
    intro v
    rw [div_eq_mul_inv, v.ord_mul hx (inv_ne_zero (pow_ne_zero n ht)), v.ord_inv,
      ← zpow_natCast t n, v.ord_zpow, htord, hord]
    ring
  obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t htr hquot
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact div_ne_zero hx (pow_ne_zero n ht) hc.symm
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_zero_of_lt hn)] at ha
    exact hc0 ha.symm
  refine ⟨t * algebraMap K F a, ?_, ?_⟩
  · rw [IntermediateField.adjoin_simple_mul_algebraMap t a ha0, hgen]
  · rw [mul_pow, ← map_pow, ha, hc, mul_div_cancel₀ _ (pow_ne_zero n ht)]

/-- Every tame finite separable rational-function-field cover unramified away from two distinct
places has generating coordinates in which its field inclusion is the degree-th power map. -/
theorem exists_power_coordinates_of_tame_two_branches
    {K F : Type} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    (v₀ v₁ : Place K (RatFunc K)) (hne : v₀ ≠ v₁)
    (htame : ∀ w : Place K F, (w.ramificationIndex (RatFunc K) : K) ≠ 0)
    (hunramified : ∀ w : Place K F, w.restrict (RatFunc K) ≠ v₀ →
      w.restrict (RatFunc K) ≠ v₁ → w.ramificationIndex (RatFunc K) = 1) :
    ∃ s : RatFunc K, ∃ t : F,
      IntermediateField.adjoin K ({s} : Set (RatFunc K)) = ⊤ ∧
      IntermediateField.adjoin K ({t} : Set F) = ⊤ ∧
      algebraMap (RatFunc K) F s = t ^ Module.finrank (RatFunc K) F := by
  classical
  obtain ⟨hcurve, heft⟩ := curve_of_finite_ratFunc (K := K) (F := F)
  have : IsCurveOver K F := hcurve
  have : Algebra.EssFiniteType K F := heft
  have : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  have : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors (Polynomial K))
  have : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  obtain ⟨s, hs, -, hsgen, hsord⟩ :=
    exists_parameter_of_genus_zero (genusFF_ratFunc_eq_zero_of_isAlgClosed K) v₀ v₁ hne
  obtain ⟨hg, h₀, h₁⟩ := genus_and_fibres_of_tame_two_branches v₀ v₁ hne htame hunramified
  obtain ⟨w₀, hw₀⟩ := Finset.card_eq_one.mp h₀
  obtain ⟨w₁, hw₁⟩ := Finset.card_eq_one.mp h₁
  have hfibre₀ : ∀ w : Place K F, w.restrict (RatFunc K) = v₀ ↔ w = w₀ := by
    intro w
    rw [← Place.mem_fiberOver, hw₀, Finset.mem_singleton]
  have hfibre₁ : ∀ w : Place K F, w.restrict (RatFunc K) = v₁ ↔ w = w₁ := by
    intro w
    rw [← Place.mem_fiberOver, hw₁, Finset.mem_singleton]
  have hwne : w₀ ≠ w₁ := by
    intro h
    exact hne (((hfibre₀ w₀).mpr rfl).symm.trans
      (h ▸ (hfibre₁ w₁).mpr rfl))
  have hindex : ∀ (v : Place K (RatFunc K)) (w : Place K F),
      v.fiberOver F = {w} → w.ramificationIndex (RatFunc K) = Module.finrank (RatFunc K) F := by
    intro v w hw
    have h := Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := F) v
    have hi := w.inertiaDeg_eq_one_of_isRational w.isRational_of_isAlgClosed
      ((w.restrict (RatFunc K)).isRational_of_isAlgClosed)
    rw [hw, Finset.sum_singleton, hi, Nat.cast_one, mul_one] at h
    exact_mod_cast h
  have h₀index := hindex v₀ w₀ hw₀
  have h₁index := hindex v₁ w₁ hw₁
  have horders : ∀ w : Place K F, w.ord (algebraMap (RatFunc K) F s) =
      (Module.finrank (RatFunc K) F : ℤ) *
        ((if w = w₀ then 1 else 0) - (if w = w₁ then 1 else 0)) := by
    intro w
    rw [w.ord_restrict, hsord]
    simp only [hfibre₀, hfibre₁]
    by_cases hzero : w = w₀
    · subst w
      rw [h₀index]
    · by_cases hone : w = w₁
      · subst w
        rw [h₁index]
      · rw [ite_eq_right hzero, ite_eq_right hone, sub_self, mul_zero, mul_zero]
  obtain ⟨t, htgen, ht⟩ := power_parameter hg w₀ w₁ hwne
    (algebraMap (RatFunc K) F s) ((map_ne_zero (algebraMap (RatFunc K) F)).mpr hs)
    (Module.finrank (RatFunc K) F) (Module.finrank_pos) horders
  exact ⟨s, t, hsgen, htgen, ht.symm⟩

/-- In characteristic zero, the power-coordinate classification needs only the two-branch
unramified condition: separability and tameness follow from the characteristic. -/
theorem exists_power_coordinates_of_two_branches_charZero
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (v₀ v₁ : Place K (RatFunc K)) (hne : v₀ ≠ v₁)
    (hunramified : ∀ w : Place K F, w.restrict (RatFunc K) ≠ v₀ →
      w.restrict (RatFunc K) ≠ v₁ → w.ramificationIndex (RatFunc K) = 1) :
    ∃ s : RatFunc K, ∃ t : F,
      IntermediateField.adjoin K ({s} : Set (RatFunc K)) = ⊤ ∧
      IntermediateField.adjoin K ({t} : Set F) = ⊤ ∧
      algebraMap (RatFunc K) F s = t ^ Module.finrank (RatFunc K) F := by
  apply exists_power_coordinates_of_tame_two_branches v₀ v₁ hne
  · intro w
    exact Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (w.ramificationIndex_pos (F := RatFunc K)))
  · exact hunramified

end AnabelianGeometry.GeometricFundamentalGroup

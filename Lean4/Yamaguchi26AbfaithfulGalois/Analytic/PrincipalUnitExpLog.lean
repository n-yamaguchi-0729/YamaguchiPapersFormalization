/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.LocalField.Analytic.MixedCharExpThreshold
import ValuedFieldTheory.LocalField.Analytic.LogExpComposition
import ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ExpConvergence
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.LogConvergence
import ValuedFieldTheory.Valuation.DiscreteValuationField.WithZeroCompleteSpace

/-!
# Exponential and logarithm on `p²𝒪_K`

Lines 460–467 of Section 3. `P` is literally `p²𝒪_K` and `U` is
`1 + p²𝒪_K`. The canonical evaluated series give inverse additive and
multiplicative homomorphisms on these sets. This statement makes no
finiteness assumption on the residue field.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

/-- The usual exponential and logarithm series are inverse group
isomorphisms between `p²𝒪_K` and `1 + p²𝒪_K`. -/
theorem principal_unit_exp_log
    {K : Type u} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    let P : Set K := {x | ∃ a : v.valuationSubring, x = (p : K) ^ 2 * (a : K)}
    let U : Set K := {u | ∃ x : K, x ∈ P ∧ u = 1 + x}
    let exp : K → K := fun x =>
      expSeriesFieldOfWithZeroValuation v x
        (fun m => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
    let log : K → K := fun u =>
      logOnePlusSeriesFieldOfWithZeroValuation v (u - 1)
        (fun m => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
    (∀ x : K, x ∈ P → exp x ∈ U) ∧
      (∀ u : K, u ∈ U → log u ∈ P) ∧
      (∀ x : K, x ∈ P → log (exp x) = x) ∧
      (∀ u : K, u ∈ U → exp (log u) = u) ∧
      (∀ x y : K, x ∈ P → y ∈ P → exp (x + y) = exp x * exp y) ∧
      (∀ u w : K, u ∈ U → w ∈ U → log (u * w) = log u + log w) := by
  let q : K := (p : K) ^ 2
  let P : Set K := {x | ∃ a : v.valuationSubring, x = q * (a : K)}
  let U : Set K := {u | ∃ x : K, x ∈ P ∧ u = 1 + x}
  have hnexp : ∀ n : ℕ, (n.factorial : K) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hnlog : ∀ n : ℕ, ((n + 1 : ℕ) : K) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  let E : K → K := fun x => expSeriesFieldOfWithZeroValuation v x hnexp
  let L : K → K := fun u => logOnePlusSeriesFieldOfWithZeroValuation v (u - 1) hnlog
  change (∀ x : K, x ∈ P → E x ∈ U) ∧
    (∀ u : K, u ∈ U → L u ∈ P) ∧
    (∀ x : K, x ∈ P → L (E x) = x) ∧
    (∀ u : K, u ∈ U → E (L u) = u) ∧
    (∀ x y : K, x ∈ P → y ∈ P → E (x + y) = E x * E y) ∧
    (∀ u w : K, u ∈ U → w ∈ U → L (u * w) = L u + L w)
  let e : ℕ := v.residueRamificationIndex p
  have hvexp : ∀ n : ℕ, v (n.factorial : K) =
      WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))) :=
    fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
      n.factorial (Nat.factorial_ne_zero n)
  have hvlog : ∀ n : ℕ, v ((n + 1 : ℕ) : K) =
      WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))) :=
    fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
      (n + 1) (Nat.succ_ne_zero n)
  have hcomplete : @CompleteSpace K (Valued.mk' v).toUniformSpace :=
    ValuationTheory.DiscreteValuationField.Valuation.completeSpace_ofWithZeroValuation v
  have hq : q ≠ 0 := by
    exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have memP_iff (z : K) : z ∈ P ↔ v z ≤ v q := by
    constructor
    · rintro ⟨a, rfl⟩
      rw [v.map_mul]
      calc
        v q * v (a : K) ≤ v q * 1 := mul_le_mul_of_nonneg_left a.property zero_le
        _ = v q := mul_one _
    · intro hz
      refine ⟨⟨z / q, ?_⟩, ?_⟩
      · change v (z / q) ≤ 1
        rw [v.map_div]
        exact (div_le_one₀ ((v.pos_iff).mpr hq)).mpr hz
      · change z = q * (z / q)
        field_simp
  have threshold {x : K} (hxP : x ∈ P) :
      ∀ hx : x ≠ 0,
        (e : ℝ) / ((p : ℝ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) := by
    obtain ⟨a, rfl⟩ := hxP
    exact fun hx => exp_threshold_natCast_sq_mul v p a hx
  have hvlt {x : K} (hxP : x ∈ P) : v x < 1 :=
    valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
      (p := p) v e (threshold hxP)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxP
    refine ⟨E x - 1, ?_, by ring⟩
    apply (memP_iff _).mpr
    by_cases hx : x = 0
    · simp only [hx, E, expSeriesField_zero_ofWithZeroValuation, sub_self, v.map_zero]
      exact zero_le
    · have hrat : (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
        exact_mod_cast threshold hxP hx
      calc
        v (E x - 1) = v x :=
          valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
            (p := p) v e hx hnexp hvexp hrat hcomplete
        _ ≤ v q := (memP_iff x).mp hxP
  · intro u hu
    obtain ⟨x, hxP, rfl⟩ := hu
    apply (memP_iff _).mpr
    change v (logOnePlusSeriesFieldOfWithZeroValuation v ((1 + x) - 1) hnlog) ≤ v q
    rw [add_sub_cancel_left]
    by_cases hx : x = 0
    · simp only [hx, logOnePlusSeriesField_zero_ofWithZeroValuation, v.map_zero]
      exact zero_le
    · have hrat : (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
        exact_mod_cast threshold hxP hx
      calc
        v (logOnePlusSeriesFieldOfWithZeroValuation v x hnlog) = v x :=
          valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
            (p := p) v e hx hnlog hvlog (hvlt hxP) hrat hcomplete
        _ ≤ v q := (memP_iff x).mp hxP
  · intro x hxP
    exact logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
      (p := p) v e x hnexp hvexp hnlog hvlog (threshold hxP) hcomplete
  · intro u hu
    obtain ⟨x, hxP, rfl⟩ := hu
    have h := expSeries_logOnePlusSeries_eq_one_add_ofWithZeroValuation_scaled_of_threshold
      (p := p) v e x hnlog hvlog hnexp hvexp (threshold hxP) hcomplete
    simpa only [L, E, add_sub_cancel_left] using h
  · intro x y hxP hyP
    exact expSeriesField_add_eq_mul_ofWithZeroValuation_scaled_of_threshold
      (p := p) v e x y hnexp hvexp (threshold hxP) (threshold hyP) hcomplete
  · intro u w hu hw
    obtain ⟨x, hxP, rfl⟩ := hu
    obtain ⟨y, hyP, rfl⟩ := hw
    have h := logOnePlusSeriesField_mul_argument_eq_add_ofWithZeroValuation_scaled
      (p := p) v e x y hnlog hvlog (hvlt hxP) (hvlt hyP) hcomplete
    simpa only [L, show (1 + x) * (1 + y) - 1 = x + y + x * y by ring,
      add_sub_cancel_left] using h

end Yamaguchi26AbfaithfulGalois

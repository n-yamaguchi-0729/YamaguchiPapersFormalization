/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharPrincipalUnitPowerWitnessLog
import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.BoundedCyclotomicCoefficient
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# A smaller logarithmic eigenvector from a power witness

An automorphism fixing the lower field fixes the logarithm of the given
principal unit. A nontrivial bounded exponent therefore produces a scalar
multiple in the same lower-field character part, still in the logarithm
image and with strictly smaller integer valuation.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {F L E : Type*} [Field F] [Field L] [Field E]
  [Algebra F L] [Algebra L E] [CharZero E]

/-- A bounded power witness produces an actual smaller lower-field
eigenvector and a principal unit whose logarithm is its image. -/
theorem exists_smaller_characterEigenvector_log_of_power_witness
    (v : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (υ : E ≃ₐ[L] E) (hval : ∀ x : E, v (υ x) = v x)
    (b : Lˣ)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)
    (hlog : (principalUnitLogOfMixedChar v p u).toAdd = algebraMap L E (b : L))
    (χ : (L ≃ₐ[F] L) → E)
    (hbeigen : ∀ γ : L ≃ₐ[F] L,
      algebraMap L E (γ (b : L)) = χ γ * algebraMap L E (b : L))
    (a s : ℕ) (ha : a < p ^ (s + 1)) (haone : a ≠ 1) (y : Eˣ)
    (hy :
      let u₀ : Eˣ :=
        (CompleteDVF.valuationSubringUnitsToFieldUnits
          (completeDVFOfWithZeroValuation v)
          (u : (completeDVFOfWithZeroValuation v).valuationSubringˣ))
      Units.map υ.toRingEquiv.toMonoidHom u₀ / u₀ ^ a = y ^ (p ^ (s + 1))) :
    ∃ (c : Lˣ)
      (z : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1),
      (∀ γ : L ≃ₐ[F] L,
        algebraMap L E (γ (c : L)) = χ γ * algebraMap L E (c : L)) ∧
      (principalUnitLogOfMixedChar v p z).toAdd = algebraMap L E (c : L) ∧
      (ofWithZeroValuation v).val (Units.map (algebraMap L E).toMonoidHom c) <
        (ofWithZeroValuation v).val (Units.map (algebraMap L E).toMonoidHom b) := by
  let q : L := (1 - (a : L)) / (p : L) ^ (s + 1)
  let qE : E := (1 - (a : E)) / (p : E) ^ (s + 1)
  have hqmap : algebraMap L E q = qE := by
    simp only [q, qE, map_div₀, _root_.map_sub, _root_.map_one,
      _root_.map_natCast, _root_.map_pow]
  have hcoeff : 1 < v qE := v.one_lt_boundedCyclotomicCoefficient p a s ha haone
  have hqE : qE ≠ 0 := (v.pos_iff).mp (lt_trans zero_lt_one hcoeff)
  have hq : q ≠ 0 := by
    intro hzero
    apply hqE
    rw [← hqmap, hzero, _root_.map_zero]
  let c : Lˣ := Units.mk0 q hq * b
  have hcmap : algebraMap L E (c : L) = qE * algebraMap L E (b : L) := by
    change algebraMap L E (q * (b : L)) = qE * algebraMap L E (b : L)
    rw [_root_.map_mul, hqmap]
  have hqfixed (γ : L ≃ₐ[F] L) : γ q = q := by
    simp only [q, map_div₀, _root_.map_sub, _root_.map_one,
      _root_.map_natCast, _root_.map_pow]
  obtain ⟨z, _hz, hzlog⟩ :=
    exists_principalUnit_log_of_fieldUnit_power_witness v p υ.toRingEquiv hval
      u a (s + 1) y hy
  refine ⟨c, z, ?_, ?_, ?_⟩
  · intro γ
    calc
      algebraMap L E (γ (c : L)) =
          algebraMap L E q * algebraMap L E (γ (b : L)) := by
        change algebraMap L E (γ (q * (b : L))) =
          algebraMap L E q * algebraMap L E (γ (b : L))
        rw [_root_.map_mul, hqfixed γ, _root_.map_mul]
      _ = χ γ * algebraMap L E (c : L) := by
        rw [hbeigen γ]
        change algebraMap L E q * (χ γ * algebraMap L E (b : L)) =
          χ γ * algebraMap L E (q * (b : L))
        rw [_root_.map_mul]
        exact mul_left_comm (algebraMap L E q) (χ γ) (algebraMap L E (b : L))
  · have hfix : υ.toRingEquiv (algebraMap L E (b : L)) = algebraMap L E (b : L) :=
      υ.commutes (b : L)
    rw [hlog, hfix] at hzlog
    refine hzlog.trans ?_
    rw [hcmap]
    change (algebraMap L E (b : L) - (a : E) * algebraMap L E (b : L)) /
        (p : E) ^ (s + 1) =
      ((1 - (a : E)) / (p : E) ^ (s + 1)) * algebraMap L E (b : L)
    rw [div_mul_eq_mul_div₀, sub_mul, one_mul]
  · apply ofWithZeroValuation_val_lt_of_valuation_lt v
    change v (algebraMap L E (b : L)) < v (algebraMap L E (c : L))
    rw [hcmap, v.map_mul]
    have hbpos : 0 < v (algebraMap L E (b : L)) :=
      (v.pos_iff).mpr ((map_ne_zero (algebraMap L E)).mpr b.ne_zero)
    simpa only [one_mul] using mul_lt_mul_of_pos_right hcoeff hbpos

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

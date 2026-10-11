/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogEquivariance
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismEquiv
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.PrimePowerRoots
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Logarithms of actual prime-power witnesses

A field-unit witness for the ratio of an automorphic principal unit and an
ordinary power is itself a principal unit. Its logarithm is determined by
the same field automorphism and power relation.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {E : Type u} [Field E] [CharZero E]

/-- A prescribed field-unit power witness lifts to the actual principal-unit
group, with its original field value and the corresponding logarithm formula. -/
theorem exists_principalUnit_log_of_fieldUnit_power_witness
    (v : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (υ : E ≃+* E) (hval : ∀ x : E, v (υ x) = v x)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)
    (a s : ℕ) (y : Eˣ)
    (hy :
      let u₀ : Eˣ :=
        (CompleteDVF.valuationSubringUnitsToFieldUnits
          (completeDVFOfWithZeroValuation v)
          (u : (completeDVFOfWithZeroValuation v).valuationSubringˣ))
      Units.map υ.toMonoidHom u₀ / u₀ ^ a = y ^ (p ^ s)) :
    ∃ z : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      (((z : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
        (completeDVFOfWithZeroValuation v).valuationSubring) : E) = (y : E) ∧
      (principalUnitLogOfMixedChar v p z).toAdd =
        (υ (principalUnitLogOfMixedChar v p u).toAdd -
          (a : E) * (principalUnitLogOfMixedChar v p u).toAdd) / (p : E) ^ s := by
  let Fv := completeDVFOfWithZeroValuation v
  have hmem (x : E) : x ∈ Fv.valuation.valuationSubring ↔
      υ x ∈ Fv.valuation.valuationSubring := by
    change v x ≤ 1 ↔ v (υ x) ≤ 1
    rw [hval x]
  let eU : CompleteDVF.higherPrincipalUnitGroup Fv 1 ≃*
      CompleteDVF.higherPrincipalUnitGroup Fv 1 :=
    CompleteDVF.higherPrincipalUnitGroup.equivOfPreserves Fv υ hmem 1
  let ι : CompleteDVF.higherPrincipalUnitGroup Fv 1 →* Eˣ :=
    (CompleteDVF.valuationSubringUnitsToFieldUnits Fv).comp
      (CompleteDVF.higherPrincipalUnitGroup Fv 1).subtype
  have hcoe (w : CompleteDVF.higherPrincipalUnitGroup Fv 1) :
      (ι w : E) = (((w : Fv.valuationSubringˣ) : Fv.valuationSubring) : E) :=
    CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply Fv
      (w : Fv.valuationSubringˣ)
  let r : CompleteDVF.higherPrincipalUnitGroup Fv 1 := eU u / u ^ a
  have hr : ι r = Units.map υ.toMonoidHom (ι u) / (ι u) ^ a := by
    change ι (eU u / u ^ a) = Units.map υ.toMonoidHom (ι u) / (ι u) ^ a
    rw [map_div, map_pow]
    apply congrArg (fun t : Eˣ => t / (ι u) ^ a)
    apply Units.ext
    rw [hcoe, Units.coe_map, hcoe]
    exact CompleteDVF.higherPrincipalUnitGroup.equivOfPreserves_apply_coe Fv υ hmem 1 u
  change Units.map υ.toMonoidHom (ι u) / (ι u) ^ a = y ^ (p ^ s) at hy
  have hroot := congrArg (fun t : Eˣ => (t : E)) (hr.trans hy).symm
  rw [Units.val_pow_eq_pow_val, hcoe] at hroot
  obtain ⟨z, hz, hzpow⟩ :=
    CompleteDVF.higherPrincipalUnitGroup.exists_primePower_root_of_field_root
      Fv p s (y : E) r hroot
      (hres := by change CharP (IsLocalRing.ResidueField v.valuationSubring) p; infer_instance)
  refine ⟨z, hz, ?_⟩
  have hlog := congrArg (principalUnitLogOfMixedChar v p) hzpow
  change principalUnitLogOfMixedChar v p (z ^ (p ^ s)) =
    principalUnitLogOfMixedChar v p (eU u / u ^ a) at hlog
  rw [map_pow, map_div, map_pow] at hlog
  have hadd := congrArg Multiplicative.toAdd hlog
  simp only [toAdd_pow, toAdd_div, nsmul_eq_mul, Nat.cast_pow] at hadd
  have haut : (principalUnitLogOfMixedChar v p (eU u)).toAdd =
      υ (principalUnitLogOfMixedChar v p u).toAdd :=
    principalUnitLogOfMixedChar_equivOfPreserves v p υ hval u
  rw [haut] at hadd
  have hp : (p : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply (eq_div_iff (pow_ne_zero s hp)).mpr
  rw [mul_comm]
  exact hadd

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

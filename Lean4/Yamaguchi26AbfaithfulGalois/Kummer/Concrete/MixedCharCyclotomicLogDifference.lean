/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicPowerWitness
import Yamaguchi26AbfaithfulGalois.Analytic.MixedCharPrincipalUnitPowerWitnessLog
import ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogLinearity
import ValuedFieldTheory.LocalField.Padic.PrimitiveRootTeichmullerCharacter

/-!
# Logarithmic action differences from trivial mod-p cohomology

The actual Kummer power witness gives a principal-unit logarithm after
subtracting the finite exponent. The exponent agrees modulo p with the
specified primitive-root character, so a p-adic power corrects that
logarithm to the actual character difference. No p-primary degree
assumption is made on the lower extension.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

-- Keep the analytic correction over an abstract field. This prevents the
-- intermediate-field scalar tower from being searched in each log identity.
private theorem log_character_difference_of_power_witness
    {F E : Type*} [Field F] [Field E] [Algebra F E] [CharZero E]
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    {ζ : E} (hζ : IsPrimitiveRoot ζ p)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1)
    (υ : Gal(E/F)) (hval : ∀ x : E, vE (υ x) = vE x)
    (a : ℕ) (ha : a < p) (hroot : υ ζ = ζ ^ a) (y : Eˣ)
    (hy : Units.map υ.toRingEquiv.toMonoidHom
        (CompleteDVF.valuationSubringUnitsToFieldUnits (completeDVFOfWithZeroValuation vE)
          (u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ)) /
        (CompleteDVF.valuationSubringUnitsToFieldUnits (completeDVFOfWithZeroValuation vE)
          (u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ)) ^ a = y ^ (p ^ 1)) :
    ∃ z : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1,
      υ (principalUnitLogOfMixedChar vE p u).toAdd -
        padicIntToFieldOfMixedChar vE p
          (primitiveRootTeichmullerCharacter F p hζ υ : ℤ_[p]) *
            (principalUnitLogOfMixedChar vE p u).toAdd =
        (p : E) * (principalUnitLogOfMixedChar vE p z).toAdd := by
  obtain ⟨c, hc⟩ := exists_primitiveRootTeichmullerCharacter_sub_natCast_eq_prime_mul
    F p hζ υ a ha hroot
  obtain ⟨z, _hzval, hzlog⟩ :=
    exists_principalUnit_log_of_fieldUnit_power_witness
      vE p υ.toRingEquiv hval u a 1 y hy
  simp only [pow_one] at hzlog
  let w := z / principalUnitPadicPowOfMixedChar vE p c u
  refine ⟨w, ?_⟩
  have hwlog : (principalUnitLogOfMixedChar vE p w).toAdd =
      (principalUnitLogOfMixedChar vE p z).toAdd -
        padicIntToFieldOfMixedChar vE p c * (principalUnitLogOfMixedChar vE p u).toAdd := by
    change (principalUnitLogOfMixedChar vE p
      (z / principalUnitPadicPowOfMixedChar vE p c u)).toAdd = _
    rw [map_div, toAdd_div, principalUnitLogOfMixedChar_padicPow]
  have hcE := congrArg (padicIntToFieldOfMixedChar vE p) hc
  rw [map_sub, _root_.map_mul, map_natCast, map_natCast] at hcE
  have hpE : (p : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hz : (p : E) * (principalUnitLogOfMixedChar vE p z).toAdd =
      υ (principalUnitLogOfMixedChar vE p u).toAdd -
        (a : E) * (principalUnitLogOfMixedChar vE p u).toAdd := by
    rw [hzlog, mul_div_cancel₀ _ hpE]
    rfl
  rw [hwlog, mul_sub, hz, ← mul_assoc, ← hcE]
  ring


variable {F K Ω : Type*} [Field F] [Field K] [Field Ω]
  [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]

/-- Trivial mod-p action produces a p-divisible character difference inside
  the actual principal-unit logarithm image. -/
theorem exists_principalUnit_log_character_difference_of_trivial_lowerH1Action
    (E : IntermediateField K Ω) [Algebra F E]
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} K E]
    [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    {ζ : E} (hζ : IsPrimitiveRoot ζ p)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1)
    (hueigen : ∀ δ : E ≃ₐ[K] E,
      δ (((u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
        (completeDVFOfWithZeroValuation vE).valuationSubring) : E) =
      (((principalUnitPadicPowOfMixedChar vE p
        (primeCyclotomicTeichmullerCharacter K E p δ : ℤ_[p]) u :
          (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
            (completeDVFOfWithZeroValuation vE).valuationSubring) : E))
    (τ : Gal(K/F)) (υ : Gal(E/F))
    (hυ : ∀ x : K, υ (algebraMap K E x) = algebraMap K E (τ x))
    (hval : ∀ x : E, vE (υ x) = vE x)
    (hτ : relativeGaloisH1Action (n := p) F K τ = 1) :
    ∃ z : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1,
      υ (principalUnitLogOfMixedChar vE p u).toAdd -
        padicIntToFieldOfMixedChar vE p
          (primitiveRootTeichmullerCharacter F p hζ υ : ℤ_[p]) *
            (principalUnitLogOfMixedChar vE p u).toAdd =
        (p : E) * (principalUnitLogOfMixedChar vE p z).toAdd := by
  have hmu : (primitiveRoots (p ^ (0 + 1)) E).Nonempty := by
    rw [Nat.zero_add, pow_one]
    exact ⟨ζ, (mem_primitiveRoots (Fact.out : p.Prime).pos).mpr hζ⟩
  have hτ' : relativeGaloisH1Action (n := p ^ (0 + 1)) F K τ = 1 := by
    exact (congrArg (fun n : ℕ => relativeGaloisH1Action (n := n) F K τ = 1)
      (pow_one p : p ^ (0 + 1) = p)).mpr hτ
  obtain ⟨a, ha, hroots, y, hy⟩ :=
    exists_cyclotomic_power_witness_of_trivial_lowerH1Action
      E vE p 0 hmu u hueigen τ υ.toRingEquiv hυ hτ'
  simp only [Nat.zero_add, pow_one] at ha hroots hy
  exact log_character_difference_of_power_witness vE p hζ u υ hval
    a ha (hroots ζ hζ.pow_eq_one) y (by simpa only [pow_one] using hy)

end ClassFieldTower.Martinet.Shafarevich

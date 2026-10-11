/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInvariantCharacter
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitPadicPowMod
import Nyll.ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerCharacter
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Invariant Kummer characters of actual cyclotomic eigenunits

The p-adic eigenunit relation supplies the power action on the field's
Kummer quotient. The actual finite cyclotomic character supplies the same
power action on all roots at the selected level. These two actions cancel
in the Kummer character.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {L E : Type*} [Field L] [Field E] [Algebra L E]

private theorem cyclotomicTeichmuller_power_action_on_roots
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} L E]
    (s : ℕ) (hmu : (primitiveRoots (p ^ (s + 1)) E).Nonempty)
    (δ : E ≃ₐ[L] E) (ξ : E) (hξ : ξ ^ (p ^ (s + 1)) = 1) :
    δ ξ = ξ ^ (PadicInt.toZModPow (s + 1)
      (primeCyclotomicTeichmullerCharacter L E p δ : ℤ_[p])).val := by
  obtain ⟨ζ, hζmem⟩ := hmu
  have hζ : IsPrimitiveRoot ζ (p ^ (s + 1)) :=
    (mem_primitiveRoots (pow_pos (Fact.out : p.Prime).pos (s + 1))).mp hζmem
  have haction := primeCyclotomicTeichmullerCharacter_spec L E p s hζ δ
  obtain ⟨i, _hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  rw [map_pow, ← haction, pow_right_comm]

/-- An actual principal unit with the finite cyclotomic p-adic eigenrelation
has a conjugation-invariant Kummer character at every positive root level
present in the field. The eigenrelation is exactly the one supplied by
`exists_minimal_cyclotomic_log_eigenunit`. -/
theorem principalUnit_cyclotomicKummerCharacter_conjugation_invariant
    [CharZero E]
    (v : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    [IsCyclotomicExtension {p} L E]
    (s : ℕ) (hmu : (primitiveRoots (p ^ (s + 1)) E).Nonempty)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)
    (hueigen : ∀ δ : E ≃ₐ[L] E,
      δ (((u : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
        (completeDVFOfWithZeroValuation v).valuationSubring) : E) =
      (((principalUnitPadicPowOfMixedChar v p
        (primeCyclotomicTeichmullerCharacter L E p δ : ℤ_[p]) u :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
            (completeDVFOfWithZeroValuation v).valuationSubring) : E))
    (δ : E ≃ₐ[L] E) (σ : Gal(AlgebraicClosure E/E)) :
    let n : ℕ+ := ⟨p ^ (s + 1), pow_pos (Fact.out : p.Prime).pos (s + 1)⟩
    let u₀ : Eˣ := CompleteDVF.valuationSubringUnitsToFieldUnits
      (completeDVFOfWithZeroValuation v)
      (u : (completeDVFOfWithZeroValuation v).valuationSubringˣ)
    absoluteKummerContinuousNthRootsCharacterEquiv E n hmu
        (u₀ : Eˣ ⧸ (powMonoidHom (n : ℕ) : Eˣ →* Eˣ).range)
        (absoluteGaloisConjugate δ.toRingEquiv σ) =
      absoluteKummerContinuousNthRootsCharacterEquiv E n hmu
        (u₀ : Eˣ ⧸ (powMonoidHom (n : ℕ) : Eˣ →* Eˣ).range) σ := by
  let Fv := completeDVFOfWithZeroValuation v
  let j : Fv.valuationSubringˣ →* Eˣ := CompleteDVF.valuationSubringUnitsToFieldUnits Fv
  let u₀ : Eˣ := j (u : Fv.valuationSubringˣ)
  let χδ : ℤ_[p]ˣ := primeCyclotomicTeichmullerCharacter L E p δ
  let a : ℕ := (PadicInt.toZModPow (s + 1) (χδ : ℤ_[p])).val
  let n : ℕ+ := ⟨p ^ (s + 1), pow_pos (Fact.out : p.Prime).pos (s + 1)⟩
  let Q := Eˣ ⧸ (powMonoidHom (n : ℕ) : Eˣ →* Eˣ).range
  have heigen : Units.map δ.toRingEquiv.toMonoidHom u₀ =
      j (principalUnitPadicPowOfMixedChar v p (χδ : ℤ_[p]) u :
        Fv.valuationSubringˣ) := by
    apply Units.ext
    exact hueigen δ
  obtain ⟨w, hw⟩ :=
    exists_fieldUnit_principalUnitPadicPow_div_natCast_eq_pow v p (χδ : ℤ_[p]) u (s + 1)
  have hdiv : Units.map δ.toRingEquiv.toMonoidHom u₀ / u₀ ^ a = w ^ (n : ℕ) := by
    rw [heigen]
    exact hw
  have hclass : ((Units.map δ.toRingEquiv.toMonoidHom u₀ : Eˣ) : Q) =
      (u₀ : Q) ^ a := by
    rw [← QuotientGroup.mk_pow]
    apply QuotientGroup.eq_iff_div_mem.mpr
    exact ⟨w, hdiv.symm⟩
  have ha : a.Coprime (n : ℕ) :=
    ZMod.val_coe_unit_coprime
      (Units.map (PadicInt.toZModPow (s + 1)).toMonoidHom χδ)
  have hroots : ∀ ξ : E, ξ ^ (n : ℕ) = 1 → δ.toRingEquiv ξ = ξ ^ a :=
    cyclotomicTeichmuller_power_action_on_roots p s hmu δ
  exact absoluteKummerContinuousNthRootsCharacterEquiv_conjugation_invariant_of_power_action
    E n hmu δ.toRingEquiv u₀ a ha hclass hroots σ

end ClassFieldTower.Martinet.Shafarevich

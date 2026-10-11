/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Analytic.LogImageProperties
import ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogLinearity
import ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogEquivariance

/-! # Lemma 3.4: the principal-unit logarithm

TeX label: `lem:principal-unit-logarithm` in `AbfatifhulGalois.tex`.
The logarithm below is the existing convergent logarithm series homomorphism.
Closure under the canonical p-adic scalars expresses the submodule assertion
without installing an additional scalar instance on the field.
-/

namespace Yamaguchi26AbfaithfulGalois

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

theorem principal_unit_logarithm_3_4
    {E : Type u} [Field E] [CharZero E]
    (v : Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    let U := CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1
    let log := principalUnitLogOfMixedChar v p
    let image : Set E := Set.range (fun u : U => (log u).toAdd)
    (∀ (f : E ≃+* E) (hval : ∀ x : E, v (f x) = v x) (u : U),
      (log (CompleteDVF.higherPrincipalUnitGroup.equivOfPreserves
        (completeDVFOfWithZeroValuation v) f
        (fun x => by change v x ≤ 1 ↔ v (f x) ≤ 1; rw [hval x]) 1 u)).toAdd =
        f (log u).toAdd) ∧
      (∀ (a : ℤ_[p]) (x : E), x ∈ image → padicIntToFieldOfMixedChar v p a * x ∈ image) ∧
      (∀ a : v.valuationSubring, (p : E) ^ 2 * (a : E) ∈ image) ∧
      (∀ x : E, (∀ n : ℕ, 0 < n → ∃ y : E, y ∈ image ∧ x = (p : E) ^ n * y) →
        x = 0) := by
  refine ⟨principalUnitLogOfMixedChar_equivOfPreserves v p, ?_, ?_, ?_⟩
  · rintro a x ⟨u, rfl⟩
    exact ⟨principalUnitPadicPowOfMixedChar v p a u,
      principalUnitLogOfMixedChar_padicPow v p a u⟩
  · intro a
    exact exists_principalUnit_log_eq_natCast_sq_mul v p a
  · intro x hx
    apply principal_unit_log_image_separated v p x
    intro n
    by_cases hn : n = 0
    · obtain ⟨y, ⟨u, hu⟩, hy⟩ := hx 1 Nat.one_pos
      dsimp only at hu
      refine ⟨u ^ p, ?_⟩
      rw [hn, pow_zero, one_mul, map_pow]
      change x = p • (principalUnitLogOfMixedChar v p u).toAdd
      rw [nsmul_eq_mul, hu]
      simpa only [pow_one] using hy
    · obtain ⟨y, ⟨u, hu⟩, hy⟩ := hx n (Nat.pos_of_ne_zero hn)
      dsimp only at hu
      exact ⟨u, by rw [hu]; exact hy⟩

end Yamaguchi26AbfaithfulGalois

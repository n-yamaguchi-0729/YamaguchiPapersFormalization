/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharCharacterLogImage
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogBound
import Mathlib.Data.Int.LeastGreatest

/-!
# Minimal valuation in a character part of an overfield's logarithm image

The set of nonzero character eigenvectors in the intermediate field whose
images are principal-unit logarithms is nonempty by a scaled normal basis.
The uniform logarithmic bound and integer-valued valuation give a minimum
in this actual intersection.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra L M] [CharZero M]

/-- The character eigenvectors in `L` that are logarithms in `M` have a least valuation. -/
theorem exists_minimal_characterEigenvector_log_image
    (v : _root_.Valuation M (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (χ : (L ≃ₐ[K] L) →* Kˣ) :
    ∃ b : Lˣ,
      (∀ σ : L ≃ₐ[K] L, σ (b : L) = (χ σ : K) • (b : L)) ∧
      (∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
        (principalUnitLogOfMixedChar v p u).toAdd = algebraMap L M (b : L)) ∧
      ∀ c : Lˣ,
        (∀ σ : L ≃ₐ[K] L, σ (c : L) = (χ σ : K) • (c : L)) →
        (∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
          (principalUnitLogOfMixedChar v p u).toAdd = algebraMap L M (c : L)) →
        (ofWithZeroValuation v).val (Units.map (algebraMap L M).toMonoidHom b) ≤
          (ofWithZeroValuation v).val (Units.map (algebraMap L M).toMonoidHom c) := by
  let P : Lˣ → Prop := fun b =>
    (∀ σ : L ≃ₐ[K] L, σ (b : L) = (χ σ : K) • (b : L)) ∧
    ∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      (principalUnitLogOfMixedChar v p u).toAdd = algebraMap L M (b : L)
  let f : Lˣ → ℤ := fun b =>
    (ofWithZeroValuation v).val (Units.map (algebraMap L M).toMonoidHom b)
  obtain ⟨m, _hm, hbound⟩ := exists_principalUnitLog_denominator_min_bound v p
  let d : ℤ := ((m + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
    (padicValNat p (m + 1) : ℤ)
  have hlower (b : Lˣ) (hb : P b) : d ≤ f b := by
    obtain ⟨u, hu⟩ := hb.2
    have hune : (principalUnitLogOfMixedChar v p u).toAdd ≠ 0 := by
      rw [hu]
      exact (map_ne_zero (algebraMap L M)).mpr b.ne_zero
    have hunit : Units.mk0 (principalUnitLogOfMixedChar v p u).toAdd hune =
        Units.map (algebraMap L M).toMonoidHom b := by
      apply Units.ext
      simpa only [Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass] using hu
    have h := hbound u hune
    rw [hunit] at h
    exact h
  obtain ⟨b₀, hb₀eigen, hb₀image⟩ := exists_nonzero_characterEigenvector_log_image v p χ
  obtain ⟨z, ⟨b, hb, hbz⟩, hz⟩ :=
    Int.exists_least_of_bdd (P := fun z => ∃ b : Lˣ, P b ∧ f b = z)
      (by
        refine ⟨d, ?_⟩
        rintro z ⟨b, hb, hbz⟩
        rw [← hbz]
        exact hlower b hb)
      ⟨f b₀, b₀, ⟨hb₀eigen, hb₀image⟩, rfl⟩
  refine ⟨b, hb.1, hb.2, ?_⟩
  intro c hceigen hcimage
  change f b ≤ f c
  rw [hbz]
  exact hz (f c) ⟨c, ⟨hceigen, hcimage⟩, rfl⟩

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

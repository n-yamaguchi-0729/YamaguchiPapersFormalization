/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.NormalBasisSubgroupCharacterVector
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogScaling
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMapExtension
import Mathlib.Algebra.CharP.Algebra

/-!
# Restricted-character vectors in the actual logarithm image

A subgroup-supported normal-basis vector is an eigenvector for the
subgroup and fails the prescribed character relation at an automorphism
outside it. Multiplying by a power of the residue prime puts the vector
in the principal-unit logarithm image and preserves both properties.

The p-adic coefficients in the base and extension fields are compared by
the actual valued-extension map. The base residue characteristic is
deduced from the extension. No normality of the subgroup, group-order
condition, or valuation-preservation assumption is used.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u v

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [CharZero E]

/-- There is a nonzero actual principal-unit logarithm which is a character
eigenvector on `Δ` and fails the same character relation at any prescribed
automorphism outside `Δ`. -/
theorem exists_principalUnit_log_subgroupCharacter_eigen_not_eigen
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vF.HasExtension vE]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    (Δ : Subgroup Gal(E/F)) (χ : Gal(E/F) →* ℤ_[p]ˣ)
    (g : Gal(E/F)) (hg : g ∉ Δ) :
    ∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1,
      (principalUnitLogOfMixedChar vE p u).toAdd ≠ 0 ∧
      (∀ δ : Δ, (δ : Gal(E/F)) (principalUnitLogOfMixedChar vE p u).toAdd =
        padicIntToFieldOfMixedChar vE p (χ (δ : Gal(E/F)) : ℤ_[p]) *
          (principalUnitLogOfMixedChar vE p u).toAdd) ∧
      g (principalUnitLogOfMixedChar vE p u).toAdd ≠
        padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) *
          (principalUnitLogOfMixedChar vE p u).toAdd := by
  have : CharP (IsLocalRing.ResidueField vF.valuationSubring) p :=
    (Algebra.charP_iff (IsLocalRing.ResidueField vF.valuationSubring)
      (IsLocalRing.ResidueField vE.valuationSubring) p).mpr inferInstance
  let χF : Gal(E/F) →* Fˣ :=
    (Units.map (padicIntToFieldOfMixedChar vF p).toMonoidHom).comp χ
  have hscalar (γ : Gal(E/F)) (x : E) :
      (χF γ : F) • x = padicIntToFieldOfMixedChar vE p (χ γ : ℤ_[p]) * x := by
    simp only [χF, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, Algebra.smul_def]
    rw [map_padicIntToFieldOfMixedChar vF vE p]
  obtain ⟨b, hb, hbeigen, hbnot⟩ :=
    exists_nonzero_subgroupCharacterEigenvector_not_eigen Δ χF g hg
  obtain ⟨n, u, hulog, hune⟩ :=
    exists_principalUnit_log_eq_natCast_pow_mul_ne_zero vE p b hb
  refine ⟨u, hune, ?_, ?_⟩
  · intro δ
    rw [hulog, _root_.map_mul, _root_.map_pow, map_natCast, hbeigen δ, hscalar]
    exact mul_left_comm ((p : E) ^ n)
      (padicIntToFieldOfMixedChar vE p (χ (δ : Gal(E/F)) : ℤ_[p])) b
  · intro hgeigen
    apply hbnot
    have hpn : (p : E) ^ n ≠ 0 :=
      pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    apply mul_left_cancel₀ hpn
    rw [hscalar]
    rw [hulog, _root_.map_mul, _root_.map_pow, map_natCast] at hgeigen
    exact hgeigen.trans (mul_left_comm
      (padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p])) ((p : E) ^ n) b)

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

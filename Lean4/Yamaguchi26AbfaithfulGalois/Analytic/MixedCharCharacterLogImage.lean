/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.LocalField.Analytic.NormalBasisCharacterEigenvector
import ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogScaling

/-!
# Nonzero character eigenvectors in an overfield's logarithm image

An eigenvector in a finite Galois extension remains in that field after
multiplication by a power of the residue prime. In a complete mixed-characteristic
overfield, a suitable such multiple is a principal-unit logarithm.
No valuation or completeness assumption on the intermediate field is needed.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra L M] [CharZero M]

/-- A nonzero character eigenvector in `L` lies in the principal-unit log image of `M`. -/
theorem exists_nonzero_characterEigenvector_log_image
    (v : _root_.Valuation M (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (χ : (L ≃ₐ[K] L) →* Kˣ) :
    ∃ b : Lˣ,
      (∀ σ : L ≃ₐ[K] L, σ (b : L) = (χ σ : K) • (b : L)) ∧
      ∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
        (principalUnitLogOfMixedChar v p u).toAdd = algebraMap L M (b : L) := by
  obtain ⟨b₀, hb₀, heigen⟩ := exists_nonzero_characterEigenvector χ
  have himage : algebraMap L M b₀ ≠ 0 := (map_ne_zero (algebraMap L M)).mpr hb₀
  obtain ⟨n, u, hlog, hlogne⟩ :=
    exists_principalUnit_log_eq_natCast_pow_mul_ne_zero v p (algebraMap L M b₀) himage
  let b : L := (p : L) ^ n * b₀
  have hmap : algebraMap L M b = (p : M) ^ n * algebraMap L M b₀ := by
    dsimp only [b]
    rw [_root_.map_mul, _root_.map_pow, _root_.map_natCast]
  have hb : b ≠ 0 := by
    intro hbzero
    apply hlogne
    rw [hlog, ← hmap, hbzero, _root_.map_zero]
  refine ⟨Units.mk0 b hb, ?_, u, hlog.trans hmap.symm⟩
  intro σ
  change σ ((p : L) ^ n * b₀) = (χ σ : K) • ((p : L) ^ n * b₀)
  rw [_root_.map_mul, _root_.map_pow, _root_.map_natCast, heigen σ, mul_smul_comm]

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

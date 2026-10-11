/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_restrict_eq_of_forall_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Place_mem_iff_ord_nonneg

/-!
# Place restrict eq of forall mem
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrict_eq_of_forall_mem

noncomputable section
open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrict_eq_of_forall_mem {K F L : Type*} [Field K] [Field F]
  [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [Algebra.IsIntegral F L]
    (w : AlgebraicCurve.Place K F) (Q : AlgebraicCurve.Place K L)
    (hQ : ∀ y ∈ w.toValuationSubring, algebraMap F L y ∈ Q.toValuationSubring) :
    Q.restrict F = w := by
  have hle : w.toValuationSubring ≤ (Q.restrict F).toValuationSubring := fun y hy => hQ y hy
  by_contra hne
  have hlt : ¬ ((Q.restrict F).toValuationSubring ≤ w.toValuationSubring) := fun hle' =>
    hne (Place.ext (le_antisymm hle' hle))
  obtain ⟨z, hzO', hzw⟩ := IsConcreteLE.not_le_iff_exists.mp hlt
  have hz0 : z ≠ 0 := fun h => hzw (h ▸ zero_mem _)
  have hordz : w.ord z < 0 := by
    by_contra h
    exact hzw ((Place.mem_iff_ord_nonneg w hz0).mpr (not_lt.mp h))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -w.ord z - 1 := ⟨(-w.ord z - 1).toNat, Int.toNat_of_nonneg
    (by omega)⟩
  have hyO' : z * (π : F) ^ k ∈ (Q.restrict F).toValuationSubring :=
    mul_mem hzO' (pow_mem (hle π.2) k)
  have hy0 : z * (π : F) ^ k ≠ 0 := mul_ne_zero hz0 (pow_ne_zero k hπ0)
  have hordy : w.ord (z * (π : F) ^ k) = -1 := by
    rw [w.ord_mul hz0 (pow_ne_zero k hπ0), ← zpow_natCast, w.ord_zpow, w.ord_coe_irreducible hπ, hk]
    ring
  apply (Q.restrict F).ne_top'
  rw [eq_top_iff]
  intro f _
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  rcases le_or_gt 0 (w.ord f) with hf | hf
  · exact hle ((Place.mem_iff_ord_nonneg w hf0).mpr hf)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -w.ord f := ⟨(-w.ord f).toNat, Int.toNat_of_nonneg
      (by omega)⟩
    have hpow0 : (z * (π : F) ^ k) ^ m ≠ 0 := pow_ne_zero m hy0
    have hg : f * ((z * (π : F) ^ k) ^ m)⁻¹ ∈ w.toValuationSubring := by
      apply (Place.mem_iff_ord_nonneg w (mul_ne_zero hf0 (inv_ne_zero hpow0))).mpr
      rw [w.ord_mul hf0 (inv_ne_zero hpow0), w.ord_inv, ← zpow_natCast, w.ord_zpow, hordy, hm]
      omega
    have : f = (f * ((z * (π : F) ^ k) ^ m)⁻¹) * (z * (π : F) ^ k) ^ m := by
      rw [inv_mul_cancel_right₀ hpow0]
    rw [this]
    exact mul_mem (hle hg) (pow_mem hyO' m)

end
end AlgebraicCurves.Places.Proofs.Place_restrict_eq_of_forall_mem
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Place restrict Along eq smul of forall eq inv smul pow
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    (p : ℕ) (hp : p ≠ 0) (g : SemilinearAut K L)
    (Φ : L →ₐ[K] L) (hΦi : Φ.toRingHom.IsIntegral) (hΦ : ∀ f : L, Φ f = (g⁻¹ • f) ^ p)
    (w : AlgebraicCurve.Place K L) :
    w.restrictAlong Φ hΦi = g • w := by
  have hpow : ∀ (A : ValuationSubring L) (y : L), y ^ p ∈ A ↔ y ∈ A := by
    intro A y
    refine ⟨fun h => ?_, fun h => A.pow_mem h p⟩
    rw [← A.valuation_le_one_iff] at h ⊢
    rw [map_pow] at h
    exact (pow_le_one_iff_of_nonneg zero_le hp).mp h
  ext1
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change Φ x ∈ w.toValuationSubring ↔ _
  rw [hΦ x, hpow]

end AlgebraicCurves.Places.Proofs.Place_restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
end ProofImplementation

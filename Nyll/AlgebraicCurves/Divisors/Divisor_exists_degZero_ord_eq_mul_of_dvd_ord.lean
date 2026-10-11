/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Divisor exists deg Zero ord eq mul of dvd ord
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_exists_degZero_ord_eq_mul_of_dvd_ord

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.exists_degZero_ord_eq_mul_of_dvd_ord {K F : Type*} [Field K]
  [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0)
    (hdvd : ∀ v : Place K F, (n : ℤ) ∣ v.ord f) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by
  obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
  have h0 : ((0 : ℤ) / (n : ℤ)) = 0 := by simp
  set D0 : Divisor K F := Finsupp.mapRange (· / (n : ℤ)) h0 Df with hD0
  have hsmul : (n : ℤ) • D0 = Df := by
    ext v
    rw [Finsupp.smul_apply, hD0, Finsupp.mapRange_apply, smul_eq_mul]
    refine Int.mul_ediv_cancel' ?_
    rw [hDf v]
    exact hdvd v
  have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
  have hdeg0 : D0 ∈ Divisor.degZero (K := K) (F := F) := by
    rw [Divisor.mem_degZero]
    have h1 : (n : ℤ) * Divisor.degree D0 = 0 := by
      rw [← smul_eq_mul, ← map_zsmul, hsmul, hdeg]
    exact (mul_eq_zero.mp h1).resolve_left hnz
  refine ⟨⟨D0, hdeg0⟩, fun v => ?_⟩
  change v.ord f = (n : ℤ) * D0 v
  rw [← hDf v, ← hsmul, Finsupp.smul_apply, smul_eq_mul]

end AlgebraicCurves.Divisors.Proofs.Divisor_exists_degZero_ord_eq_mul_of_dvd_ord
end ProofImplementation

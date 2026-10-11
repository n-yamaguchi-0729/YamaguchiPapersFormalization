/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Divisor inv smul D eq inv smul D of is Principal sub
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace DlogRecipeWD

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem D_pow_char (p : ℕ) [CharP K p] (h : F) : D K F (h ^ p) = 0 := by
  have : CharP F p := (algebraMap K F).charP_iff_charP p |>.mp inferInstance
  rw [Derivation.leibniz_pow, smul_comm, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul,
    smul_zero]

theorem dlog_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ • D K F (a * b) = a⁻¹ • D K F a + b⁻¹ • D K F b := by
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, mul_inv, add_comm]
  congr 1
  · rw [show a⁻¹ * b⁻¹ * b = a⁻¹ from inv_mul_cancel_right₀ hb _]
  · rw [show a⁻¹ * b⁻¹ * a = b⁻¹ by rw [mul_comm a⁻¹, inv_mul_cancel_right₀ ha]]

theorem dlog_algebraMap (c : K) : (algebraMap K F c)⁻¹ • D K F (algebraMap K F c) = 0 := by
  rw [Derivation.map_algebraMap, smul_zero]

theorem dlog_eq_of_isPrincipal_sub (p : ℕ) [CharP K p]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
    {D₁ D₂ : Divisor K F} (h : Divisor.IsPrincipal (D₁ - D₂))
    {f₁ f₂ : F} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ v : Place K F, (p : ℤ) * D₁ v = v.ord f₁)
    (h₂ : ∀ v : Place K F, (p : ℤ) * D₂ v = v.ord f₂) :
    f₁⁻¹ • D K F f₁ = f₂⁻¹ • D K F f₂ := by
  obtain ⟨h, hh, hDh⟩ := h
  have hhp : h ^ p ≠ 0 := pow_ne_zero _ hh
  set u : F := f₁ * (f₂ * h ^ p)⁻¹ with hu_def
  have hu0 : u ≠ 0 := mul_ne_zero hf₁ (inv_ne_zero (mul_ne_zero hf₂ hhp))
  have hu : ∀ v : Place K F, v.ord u = 0 := fun v => by
    rw [hu_def, v.ord_mul hf₁ (inv_ne_zero (mul_ne_zero hf₂ hhp)), v.ord_inv,
      v.ord_mul hf₂ hhp, ← h₁ v, ← h₂ v]
    have hp : v.ord (h ^ p) = (p : ℤ) * v.ord h := by
      rw [← zpow_natCast, v.ord_zpow]
    rw [hp, ← hDh v, Finsupp.sub_apply]
    ring
  obtain ⟨c, hc⟩ := hconst u hu0 hu
  have hf₁' : f₁ = algebraMap K F c * (f₂ * h ^ p) := by
    rw [hc, hu_def, inv_mul_cancel_right₀ (mul_ne_zero hf₂ hhp)]
  have hc0 : algebraMap K F c ≠ 0 := by rw [hc]; exact hu0
  rw [hf₁', dlog_mul hc0 (mul_ne_zero hf₂ hhp), dlog_algebraMap, zero_add, dlog_mul hf₂ hhp,
    D_pow_char p, smul_zero, add_zero]

end DlogRecipeWD

end AlgebraicCurve

end

theorem _root_.AlgebraicCurve.Divisor.inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
    (K F : Type*) [Field K] [Field F] [Algebra K F] (p : ℕ) [CharP K p]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : AlgebraicCurve.Place K F, v.ord u = 0) →
      u ∈ (algebraMap K F).range)
    (D₁ D₂ : AlgebraicCurve.Divisor K F) (h : AlgebraicCurve.Divisor.IsPrincipal (D₁ - D₂))
    (f₁ f₂ : F) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₁ v = v.ord f₁)
    (h₂ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₂ v = v.ord f₂) :
    f₁⁻¹ • KaehlerDifferential.D K F f₁ = f₂⁻¹ • KaehlerDifferential.D K F f₂ :=
  AlgebraicCurve.DlogRecipeWD.dlog_eq_of_isPrincipal_sub p hconst h hf₁ hf₂ h₁ h₂
end AlgebraicCurves.Divisors.Proofs.Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
end ProofImplementation

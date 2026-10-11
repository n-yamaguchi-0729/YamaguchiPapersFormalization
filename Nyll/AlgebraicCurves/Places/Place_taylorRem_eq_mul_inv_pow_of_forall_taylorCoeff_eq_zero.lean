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

import Nyll.AlgebraicCurves.Places.Taylor

/-!
# Place taylor Rem eq mul inv pow of forall taylor Coeff eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorRem v t f e = f * t⁻¹ ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [taylorRem_succ', h e (Nat.lt_succ_self e), map_zero, sub_zero,
      ih (fun q hq => h q (Nat.lt_succ_of_lt hq)), pow_succ, mul_assoc]
end AlgebraicCurves.Places.Proofs.Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero
end ProofImplementation

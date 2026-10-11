/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import AlgebraicCurves.Places.Taylor
import AlgebraicCurves.Places.Place_taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero

/-!
# Place taylor Coeff eq eval At mul inv pow of forall taylor Coeff eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) {e : ℕ} (h : ∀ q, q < e → taylorCoeff v t q f = 0) :
    taylorCoeff v t e f = v.evalAt (f * t⁻¹ ^ e) := by
  rw [taylorCoeff_eq, taylorRem_eq_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f h]
end Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
end AlgebraicCurves.Places.Proofs
end ProofImplementation

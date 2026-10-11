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

import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Places.Place_evalAt_mul
import AlgebraicCurves.Places.Place_mem_of_ord_nonneg

/-!
# Place evalAt inv

Evaluation at a rational place preserves inversion for a nonzero function of order zero.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_inv

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.evalAt_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) : v.evalAt f⁻¹ =
  (v.evalAt f)⁻¹ := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, neg_zero]
  have hmul := v.evalAt_mul hv (v.mem_of_ord_nonneg hf h.ge) (v.mem_of_ord_nonneg hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm
end AlgebraicCurves.Places.Proofs.Place_evalAt_inv
end ProofImplementation

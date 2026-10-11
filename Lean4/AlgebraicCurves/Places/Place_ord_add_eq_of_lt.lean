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

import AlgebraicCurves.Divisors.ClassGroup

/-!
# Place ord add eq of lt

The order of a sum equals the smaller order when the two nonzero summands have unequal orders.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_add_eq_of_lt

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace FF2S
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_add_eq_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    have hf' := v.adicValuation_ne_zero hf
    have hg' := v.adicValuation_ne_zero hg
    rw [← WithZero.log_lt_log hg' hf']
    unfold Place.ord at h
    omega
  unfold Place.ord
  rw [Valuation.map_add_eq_of_lt_left _ hval]

end AlgebraicCurve.FF2S

theorem _root_.AlgebraicCurve.Place.ord_add_eq_of_lt {K F : Type*} [Field K] [Field F]
  [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h :
  v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f :=
  AlgebraicCurve.FF2S.ord_add_eq_of_lt v hf hg h
end AlgebraicCurves.Places.Proofs.Place_ord_add_eq_of_lt
end ProofImplementation

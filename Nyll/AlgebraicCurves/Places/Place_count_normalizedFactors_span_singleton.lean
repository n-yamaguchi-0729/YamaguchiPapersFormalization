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

import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Places.Place_le_ord_iff_mem_pow_fiberCenter
import Nyll.AlgebraicCurves.Places.Place_ord_nonneg_of_mem

/-!
# Place count normalized Factors span singleton
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_count_normalizedFactors_span_singleton

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid AlgebraicCurve
  AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.count_normalizedFactors_span_singleton {K F F' : Type*} [Field
  K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'}
    (hw : w.restrict F = v) {c : integralClosureAt F' v} (hc : c ≠ 0) :
    (normalizedFactors (Ideal.span {c})).count (fiberCenter F' v hw).asIdeal
      = (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat := by
  have : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  have hord0 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) :=
    w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw c)
  refine Ideal.count_normalizedFactors_eq (p := (fiberCenter F' v hw).asIdeal)
    (x := Ideal.span {c})
    (n := (w.ord (algebraMap (integralClosureAt F' v) F' c)).toNat) ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, ← AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw
      hc]
    omega
  · rw [Ideal.span_singleton_le_iff_mem, ← AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter hw
      hc]
    push_cast
    omega
end AlgebraicCurves.Places.Proofs.Place_count_normalizedFactors_span_singleton
end ProofImplementation

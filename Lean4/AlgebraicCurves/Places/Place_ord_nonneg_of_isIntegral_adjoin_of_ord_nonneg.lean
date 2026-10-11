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

import AlgebraicCurves.Places.Place_mem_toValuationSubring_of_isIntegral_adjoin
import AlgebraicCurves.Places.Place_ord_nonneg_of_mem
import AlgebraicCurves.Places.Place_mem_iff_ord_nonneg
import AlgebraicCurves.Divisors.ClassGroup

/-!
# Place ord nonneg of is Integral adjoin of ord nonneg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

private theorem ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg_impl {K F : Type*} [Field K] [Field
  F] [Algebra K F]
    (v : Place K F) {j u : F} (hu : IsIntegral (Algebra.adjoin K {j}) u) (hj : 0 ≤ v.ord j) :
    0 ≤ v.ord u := by
  have hjmem : j ∈ v.toValuationSubring := by
    rcases eq_or_ne j 0 with rfl | hj0
    · exact zero_mem _
    · exact (v.mem_iff_ord_nonneg hj0).mpr hj
  exact v.ord_nonneg_of_mem (v.mem_toValuationSubring_of_isIntegral_adjoin hjmem hu)

end AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg {K F : Type*}
  [Field K] [Field F]
    [Algebra K F] (v : AlgebraicCurve.Place K F) {j u : F} (hu : IsIntegral (Algebra.adjoin K {j})
      u)
    (hj : 0 ≤ v.ord j) : 0 ≤ v.ord u :=
  AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg_impl v hu hj
end AlgebraicCurves.Places.Proofs.Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
end ProofImplementation

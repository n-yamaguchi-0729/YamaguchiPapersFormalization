/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Taylor
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions

/-!
# Place taylor Rem mem to Valuation Subring
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_mem_toValuationSubring

open AlgebraicCurve AlgebraicCurve.Place

namespace ProofAuxJetT1

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_sub_of_mem' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem ord_nonneg_of_mem' (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem sub_evalAt_mul_inv_mem' (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    (g - algebraMap K F (v.evalAt g)) * t⁻¹ ∈ v.toValuationSubring := by
  have hc : algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hx : g - algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := sub_mem hg hc
  by_cases hx0 : g - algebraMap K F (v.evalAt g) = 0
  · rw [hx0, zero_mul]; exact zero_mem _
  have ht0 : t ≠ 0 := by rintro rfl; simp [Place.ord_zero] at ht
  have hval : v.evalAt (g - algebraMap K F (v.evalAt g)) = 0 := by
    rw [ProofAuxJetT1.evalAt_sub_of_mem' v hv hg hc, v.evalAt_algebraMap_eq, sub_self]
  have hord0 : v.ord (g - algebraMap K F (v.evalAt g)) ≠ 0 := fun h0 =>
    v.evalAt_ne_zero_of_ord_eq_zero hv hx0 h0 hval
  have hord1 : 1 ≤ v.ord (g - algebraMap K F (v.evalAt g)) := by
    have := ProofAuxJetT1.ord_nonneg_of_mem' v hx hx0; omega
  apply v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hx0 (inv_ne_zero ht0))
  rw [v.ord_mul hx0 (inv_ne_zero ht0), v.ord_inv, ht]
  omega

end ProofAuxJetT1

theorem _root_.AlgebraicCurve.Place.taylorRem_mem_toValuationSubring
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (r : ℕ) :
    taylorRem v t f r ∈ v.toValuationSubring := by
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    rw [taylorRem_succ]
    exact ProofAuxJetT1.sub_evalAt_mul_inv_mem' v hv ht ih
end AlgebraicCurves.Places.Proofs.Place_taylorRem_mem_toValuationSubring
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Places.Place_exists_forall_adicValuation_sub_le
import Nyll.AlgebraicCurves.Places.Place_exists_forall_ord_eq_finset
import Nyll.AlgebraicCurves.Places.Place_ord_add_eq_of_lt
import Nyll.AlgebraicCurves.Places.OverDVR

/-!
# Place exists forall adicValuation sub eq

Weak approximation realizes prescribed nonzero adic distances from given values at finitely many
places.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_forall_adicValuation_sub_eq

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.exists_forall_adicValuation_sub_eq {K F : Type*} [Field K]
  [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) (β : AlgebraicCurve.Place K F → F)
    (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ f : F, ∀ v ∈ T, v.adicValuation (f - β v) = WithZero.exp (n v) := by
  obtain ⟨f₀, hf₀⟩ := Place.exists_forall_adicValuation_sub_le T β (fun v => n v - 1)
  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq_finset T (fun v => -n v)
  refine ⟨f₀ + g, fun v hv => ?_⟩
  have hgv : v.ord g = -n v := hg v hv
  have hval_g : v.adicValuation g = WithZero.exp (n v) := by
    rw [v.adicValuation_eq_exp_neg_ord hg0, hgv, neg_neg]
  have hsplit : f₀ + g - β v = g + (f₀ - β v) := by ring
  rw [hsplit]
  rcases eq_or_ne (f₀ - β v) 0 with h0 | h0
  · rw [h0, add_zero, hval_g]
  · have hord : 1 - n v ≤ v.ord (f₀ - β v) := by
      have := (v.adicValuation_le_exp_iff).mp (hf₀ v hv)
      rcases this with h | h
      · exact absurd h h0
      · omega
    have hlt : v.ord g < v.ord (f₀ - β v) := by rw [hgv]; omega
    have hne : g + (f₀ - β v) ≠ 0 := by
      intro hz
      rw [eq_neg_of_add_eq_zero_right hz, v.ord_neg] at hlt
      exact lt_irrefl _ hlt
    rw [v.adicValuation_eq_exp_neg_ord hne, v.ord_add_eq_of_lt hg0 h0 hlt, hgv, neg_neg]
end AlgebraicCurves.Places.Proofs.Place_exists_forall_adicValuation_sub_eq
end ProofImplementation

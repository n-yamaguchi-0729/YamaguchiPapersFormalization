/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_evalAt_congr.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Place evalAt congr

Evaluation at a place is unchanged when two integral functions have the same residue.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_evalAt_congr
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open IsDedekindDomain WithZero IsLocalRing AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.evalAt_congr {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) (h :
  f - g = 0 ∨ 0 < v.ord (f - g)) : v.evalAt f = v.evalAt g := by
  rcases h with h | h
  · rw [sub_eq_zero] at h
    rw [h]
  have hsub : f - g ∈ v.toValuationSubring := sub_mem hf hg
  have hmax : ∀ {x : F} (hx : x ∈ v.toValuationSubring), 0 < v.ord x →
      (⟨x, hx⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    intro x hx hpos
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Submodule.zero_mem _
    rw [v.mem_maximalIdeal_iff_adicValuation_lt_one]
    have hne : v.adicValuation x ≠ 0 := v.adicValuation_ne_zero hx0
    rw [← exp_log hne, show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
    have : v.ord x = -log (v.adicValuation x) := rfl
    omega
  have hmem : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    have : (⟨f, hf⟩ : v.toValuationSubring) - ⟨g, hg⟩ = ⟨f - g, hsub⟩ := rfl
    rw [this]
    exact hmax hsub h
  have hres : residue v.toValuationSubring (⟨f, hf⟩ : v.toValuationSubring)
      = residue v.toValuationSubring (⟨g, hg⟩ : v.toValuationSubring) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [v.evalAt_of_mem hf, v.evalAt_of_mem hg, hres]
end AlgebraicCurves.Places.Proofs.Place_evalAt_congr
end ProofImplementation

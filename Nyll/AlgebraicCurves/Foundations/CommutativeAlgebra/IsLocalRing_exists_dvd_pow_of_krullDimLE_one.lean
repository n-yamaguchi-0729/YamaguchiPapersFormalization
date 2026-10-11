/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Is Local Ring exists dvd pow of krull Dim LE one
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_exists_dvd_pow_of_krullDimLE_one

open IsLocalRing

namespace RankOneNilSol

theorem exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  by_cases hu : IsUnit b
  · exact ⟨0, hu.dvd⟩
  · have hne : Ideal.span {b} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hrad : (Ideal.span {b}).radical = maximalIdeal R := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hne, inferInstance⟩) (le_sInf ?_)
      rintro J ⟨hJ, hJp⟩
      have hJ0 : J ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hJ
        exact hb hJ
      exact (IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJ0)).ge
    have hc' : c ∈ (Ideal.span {b}).radical := hrad ▸ hc
    obtain ⟨n, hn⟩ := hc'
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end RankOneNilSol

theorem _root_.IsLocalRing.exists_dvd_pow_of_krullDimLE_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ IsLocalRing.maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n :=
  RankOneNilSol.exists_dvd_pow hb hc
end IsLocalRing_exists_dvd_pow_of_krullDimLE_one
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

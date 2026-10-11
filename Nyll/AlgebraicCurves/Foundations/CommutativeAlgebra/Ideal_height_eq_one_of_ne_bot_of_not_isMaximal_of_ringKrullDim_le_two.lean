/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Ideal height eq one of ne bot of not is Maximal of ring Krull Dim le two
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two

theorem _root_.Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥) (hPm : ¬ P.IsMaximal) :
    P.height = 1 := by
  have := Ideal.finiteHeight_of_isNoetherianRing P
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hPtop
  have hPM' : P < M := lt_of_le_of_ne hPM (fun h => hPm (h ▸ hM))
  have := hM.isPrime
  have hM2 : M.height ≤ ((2 : ℕ) : ℕ∞) := by
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    have h2 : ((M.height : ℕ∞) : WithBot ℕ∞) ≤ (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h.trans
      (by exact_mod_cast hdim)
    exact WithBot.coe_le_coe.mp h2
  have hlt : P.height < ((2 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hM2) P inferInstance hPM'
  have hne0 : P.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    exact hP0
  have hfin : P.height ≠ ⊤ := Ideal.height_ne_top hPtop
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hk] at hlt hne0 ⊢
  norm_cast at hlt hne0 ⊢
  omega
end Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

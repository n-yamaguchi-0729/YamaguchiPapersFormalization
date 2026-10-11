/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin

/-!
# Valuation Subring finite prime Spectrum of ring Krull Dim lt top
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top

namespace AbhFinSol

open ValuationSubring

lemma finite_of_krullDim_lt_top (P : Type*) [LinearOrder P] (h : Order.krullDim P < ⊤) :
    Finite P := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  have hn : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ Order.krullDim P := by
    intro n
    rw [Order.le_krullDim_iff]
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq P (n + 1)
    refine ⟨⟨n, fun i => s.orderEmbOfFin hs i, fun i => ?_⟩, rfl⟩
    exact (s.orderEmbOfFin hs).strictMono (Fin.castSucc_lt_succ)
  have htop : Order.krullDim P = ⊤ := by
    have hne : Order.krullDim P ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr inferInstance
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
    rw [← hd] at hn ⊢
    have hd' : d = ⊤ := ENat.eq_top_iff_forall_ge.mpr (fun m => by exact_mod_cast hn m)
    rw [hd']; rfl
  exact h.ne htop

end AbhFinSol

open AbhFinSol in
theorem _root_.ValuationSubring.finite_primeSpectrum_of_ringKrullDim_lt_top {L : Type*} [Field L]
  (A : ValuationSubring L) (h : ringKrullDim A < ⊤) :
    Finite (PrimeSpectrum A) := by
  have e := ValuationSubring.primeSpectrumOrderEquiv A
  have hdim : Order.krullDim {S // A ≤ S} < ⊤ := by
    rw [← Order.krullDim_eq_of_orderIso e, Order.krullDim_orderDual]; exact h
  have hfin : Finite {S // A ≤ S} := finite_of_krullDim_lt_top _ hdim
  exact Finite.of_equiv _ e.toEquiv.symm
end AlgebraicCurves.Valuations.Proofs.ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top
end ProofImplementation

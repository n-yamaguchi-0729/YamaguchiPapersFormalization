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

import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.GoingDown

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal

/-!
# Is Local Ring two le ring Krull Dim adic Completion of two le
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le

theorem _root_.IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  have : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  have h2 : (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum R) := by
    change ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R
    exact h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := AdicCompletion (IsLocalRing.maximalIdeal R) R) l.last
  have : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
  have := Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  exact this
end IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

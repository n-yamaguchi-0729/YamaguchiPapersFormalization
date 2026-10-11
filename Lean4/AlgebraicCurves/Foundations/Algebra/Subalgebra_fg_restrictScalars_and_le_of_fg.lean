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

import Mathlib.RingTheory.Adjoin.FG

/-!
# Subalgebra fg restrict Scalars and le of fg
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Subalgebra_fg_restrictScalars_and_le_of_fg

universe u

theorem _root_.Subalgebra.fg_restrictScalars_and_le_of_fg
    {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (T : Subalgebra A₀ A) (hT : T.FG) (T' : Subalgebra ↥T A) (hT' : T'.FG) :
    (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by
  classical
  obtain ⟨s, rfl⟩ := hT
  obtain ⟨t, rfl⟩ := hT'
  have key : (Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s : Set A))) (↑t : Set A)).restrictScalars A₀ =
      Algebra.adjoin A₀ ((↑s : Set A) ∪ ↑t) :=
    (Algebra.adjoin_union_eq_adjoin_adjoin A₀ (↑s : Set A) ↑t).symm
  refine ⟨⟨s ∪ t, ?_⟩, ?_⟩
  · rw [key, Finset.coe_union]
  · rw [key]
    exact Algebra.adjoin_mono Set.subset_union_left
end AlgebraicCurves.Foundations.Algebra.Proofs.Subalgebra_fg_restrictScalars_and_le_of_fg
end ProofImplementation

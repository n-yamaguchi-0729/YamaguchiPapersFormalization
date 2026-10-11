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

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# One-dimensional fibers after base change

Transfers rank one at every prime to dimension one over a field algebra.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one

universe u

open TensorProduct

theorem _root_.Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    {R : Type u} [CommRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Flat R P]
    (h : ∀ 𝔭, Module.rankAtStalk (R := R) P 𝔭 = 1)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] P) = 1 := by
  have hq : Module.rankAtStalk (R := K) (K ⊗[R] P) ⟨⊥, Ideal.isPrime_bot⟩ = 1 := by
    rw [Module.rankAtStalk_baseChange]; exact h _
  rw [Module.rankAtStalk_eq_finrank_tensorProduct] at hq
  have : Nontrivial (Localization.AtPrime (⊥ : Ideal K)) := by infer_instance
  rwa [Module.finrank_baseChange] at hq
end Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

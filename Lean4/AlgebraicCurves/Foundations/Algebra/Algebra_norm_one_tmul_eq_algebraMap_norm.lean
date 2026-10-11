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

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Norm.Defs

/-!
# Algebra norm one tmul eq algebra Map norm
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_tmul_eq_algebraMap_norm

universe u v w

open scoped TensorProduct

theorem _root_.Algebra.norm_one_tmul_eq_algebraMap_norm
    {K : Type u} [CommRing K] {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite
      K L]
    (K' : Type w) [CommRing K'] [Algebra K K'] (x : L) :
    Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by
  classical
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul c l => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_tmul_eq_algebraMap_norm
end ProofImplementation

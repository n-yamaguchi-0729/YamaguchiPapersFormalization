/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_one_add_eps_tmul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs

/-!
# Algebra norm one add eps tmul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_add_eps_tmul

universe u

open scoped TensorProduct

theorem _root_.Algebra.norm_one_add_eps_tmul
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A'
      B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A')
      ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by
  classical
  let b := Module.Free.chooseBasis A' B
  let b' : Module.Basis (Module.Free.ChooseBasisIndex A' B) (DualNumber A') (DualNumber A' ⊗[A'] B)
    :=
    Algebra.TensorProduct.basis (DualNumber A') b
  have hM : ∀ g : B, Algebra.leftMulMatrix b' ((1 : DualNumber A') ⊗ₜ[A'] g)
      = (Algebra.leftMulMatrix b g).map (algebraMap A' (DualNumber A')) := by
    intro g
    have hlmul : Algebra.lmul (DualNumber A') (DualNumber A' ⊗[A'] B) ((1 : DualNumber A') ⊗ₜ[A'] g)
        = (Algebra.lmul A' B g).baseChange (DualNumber A') := by
      apply b'.ext
      intro k
      simp [b', Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.leftMulMatrix_apply, hlmul, LinearMap.toMatrix_baseChange,
      Algebra.leftMulMatrix_apply]
  have hone : Algebra.leftMulMatrix (R := DualNumber A') (S := DualNumber A' ⊗[A'] B) b' 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hM 1, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f
      = (DualNumber.eps : DualNumber A') • ((1 : DualNumber A') ⊗ₜ[A'] f) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hadd : Algebra.leftMulMatrix b' ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber
    A') ⊗ₜ[A'] f)
      = 1 + (DualNumber.eps : DualNumber A') • (Algebra.leftMulMatrix b f).map (algebraMap A'
        (DualNumber A')) := by
    rw [h1]
    simp only [map_add, map_smul, hone, hM]
  rw [Algebra.norm_eq_matrix_det b', hadd, Matrix.det_one_add_smul,
    pow_two, DualNumber.eps_mul_eps, mul_zero, add_zero,
    ← AddMonoidHom.map_trace (algebraMap A' (DualNumber A')), ← Algebra.trace_eq_matrix_trace b f,
    DualNumber.inr_eq_smul_eps]
  exact congrArg (fun z : DualNumber A' => 1 + z)
    (Algebra.smul_def (R := A') (A := DualNumber A')
      (Algebra.trace A' B f) DualNumber.eps).symm
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_add_eps_tmul
end ProofImplementation

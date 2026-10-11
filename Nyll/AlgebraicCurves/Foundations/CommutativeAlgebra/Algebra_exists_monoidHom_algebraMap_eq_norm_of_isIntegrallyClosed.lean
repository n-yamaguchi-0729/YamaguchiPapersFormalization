/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.Choose

/-!
# Algebra exists monoid Hom algebra Map eq norm of is Integrally Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraExistsMonoidHomAlgebraMap

universe u v w w'

theorem _root_.Algebra.exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
      [Algebra A B]
    [Algebra.IsIntegral A B]
    (K : Type w) (L : Type w') [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
    ∃ N : B →* A, ∀ b : B, algebraMap A K (N b) = Algebra.norm K (algebraMap B L b) := by
  classical
  have hmem : ∀ b : B, ∃ a : A, algebraMap A K a = Algebra.norm K (algebraMap B L b) := by
    intro b
    have hb : IsIntegral A (algebraMap B L b) := (Algebra.IsIntegral.isIntegral (R := A)
      b).algebraMap
    have hn : IsIntegral A (Algebra.norm K (algebraMap B L b)) := Algebra.isIntegral_norm K hb
    exact IsIntegrallyClosed.isIntegral_iff.mp hn
  choose N hN using hmem
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  refine ⟨{ toFun := N, map_one' := ?_, map_mul' := ?_ }, fun b => hN b⟩
  · apply hinj
    rw [hN, map_one, map_one, map_one]
  · intro b c
    apply hinj
    rw [hN, map_mul, map_mul, map_mul, hN, hN]
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraExistsMonoidHomAlgebraMap
end ProofImplementation

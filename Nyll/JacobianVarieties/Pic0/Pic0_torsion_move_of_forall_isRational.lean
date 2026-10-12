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

import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.JacobianVarieties.Pic0.Pic0_exists_mk_eq_forall_notMem_support

/-!
Represent a torsion Picard class by a divisor avoiding a prescribed finite set of places.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_torsion_move_of_forall_isRational


noncomputable section

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.torsion.move_of_forall_isRational {K F : Type*} [Field K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F] (hrat : ∀ v : Place K F, v.IsRational)
    (n : ℕ) (x : Pic0.torsion K F n) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S) := by
  obtain ⟨D, hD, hS⟩ := Pic0.exists_mk_eq_forall_notMem_support (x : Pic0 K F) S
  exact ⟨D, hD, fun v _ => hrat v, hS⟩

end
end JacobianVarieties.Pic0.Proofs.Pic0_torsion_move_of_forall_isRational
end ProofImplementation

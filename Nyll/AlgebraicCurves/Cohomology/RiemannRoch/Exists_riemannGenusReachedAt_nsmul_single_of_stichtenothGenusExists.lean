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

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_of_genusReached
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace

/-!
# Exists riemann Genus Reached At nsmul single of stichtenoth Genus Exists
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsGenusReachedNsmulSingle

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, RiemannGenusReachedAt γ ((n : ℤ) • Finsupp.single Q 1) := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached h Q
  refine ⟨n, ?_⟩
  have hidx := (indexOfSpecialty_eq_of_genusReached h
    ((n : ℤ) • Finsupp.single Q (1 : ℤ))).2
  rw [hn] at hidx
  have heq : Divisor.degree ((n : ℤ) • Finsupp.single Q (1 : ℤ)) -
      (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) = γ - 1 := by
    push_cast at hidx ⊢
    linarith
  exact ⟨finiteDimensional_lSpace _, heq, h.isMax⟩
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsGenusReachedNsmulSingle
end ProofImplementation

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

import AlgebraicCurves.Geometry.Schemes.MumfordTruncation
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_finite_K0
import AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_flat_K0
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.FinitePresentation

/-!
Projectivity of the enlarged kernel in the finite-presentation construction.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_projective_K0

noncomputable section

open scoped TensorProduct

universe u v w

open TwoChartCech.Mumford in
theorem _root_.TwoChartCech.Mumford.projective_K0
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range
      d)] :
    Module.Projective R (TwoChartCech.Mumford.K0 d) := by
  have := TwoChartCech.Mumford.finite_K0 d
  have := TwoChartCech.Mumford.flat_K0 d
  have : Module.FinitePresentation R (K0 d) := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

end
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_projective_K0
end ProofImplementation

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

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite Along of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FiniteAlong_of_isIntegral

open AlgebraicCurve

theorem _root_.AlgebraicCurve.finiteAlong_of_isIntegral
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    FiniteAlong K φ := by
  classical
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  obtain ⟨s, hs⟩ := IntermediateField.fg_top F F'
  have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [hs] at hfin
  change Module.Finite F F'
  exact (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv.finiteDimensional
end AlgebraicCurves.FunctionFields.Proofs.FiniteAlong_of_isIntegral
end ProofImplementation

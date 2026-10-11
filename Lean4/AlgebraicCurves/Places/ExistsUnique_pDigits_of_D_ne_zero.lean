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

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Places.PDigits_existsUnique

/-!
# Exists Unique p Digits of D ne zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.ExistsUnique_pDigits_of_D_ne_zero

theorem _root_.AlgebraicCurve.existsUnique_pDigits_of_D_ne_zero {K : Type*} {F : Type*} [Field K]
  [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : KaehlerDifferential.D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) :=
  AlgebraicCurve.pDigits_existsUnique p x hdt g
end AlgebraicCurves.Places.Proofs.ExistsUnique_pDigits_of_D_ne_zero
end ProofImplementation

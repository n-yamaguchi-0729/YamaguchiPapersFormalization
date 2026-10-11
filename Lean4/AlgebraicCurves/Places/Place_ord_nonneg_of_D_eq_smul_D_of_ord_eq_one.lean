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
import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Places.Place_D_ne_zero_of_ord_eq_one
import AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField

/-!
# Place ord nonneg of D eq smul D of ord eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_nonneg_of_D_eq_smul_D_of_ord_eq_one

theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_D_eq_smul_D_of_ord_eq_one {K F : Type*} [Field K]
  [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
      {t : F}
    (ht : v.ord t = 1) {f : F} (hf : 0 ≤ v.ord f) {g : F}
    (hg : KaehlerDifferential.D K F f = g • KaehlerDifferential.D K F t) :
    0 ≤ v.ord g := by
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  have hdt : KaehlerDifferential.D K F t ≠ 0 := AlgebraicCurve.Place.D_ne_zero_of_ord_eq_one x v ht
  have hcoef : AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f) = g := by
    apply smul_left_injective F hdt
    simp only
    rw [AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, hg⟩, hg]
  rw [← hcoef]
  exact AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht hf
end AlgebraicCurves.Places.Proofs.Place_ord_nonneg_of_D_eq_smul_D_of_ord_eq_one
end ProofImplementation

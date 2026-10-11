/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Mathlib.FieldTheory.RatFunc.Degree
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_placeInfty
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Evaluation

/-!
# Rational Function Field ord place Infty algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_ord_placeInfty_algebraMap
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem _root_.AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap {K : Type*} [Field K]
  [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap
  (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by
  rw [AlgebraicCurve.RationalFunctionField.ord_placeInfty (RatFunc.algebraMap_ne_zero hq),
    RatFunc.intDegree_polynomial]
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_ord_placeInfty_algebraMap
end ProofImplementation

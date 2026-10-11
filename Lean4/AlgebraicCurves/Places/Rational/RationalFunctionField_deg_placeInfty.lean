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

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import AlgebraicCurves.Places.Rational.Infinity
import AlgebraicCurves.Places.Rational.Classification
import AlgebraicCurves.Places.Rational.RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.Places.Evaluation

/-!
# RationalFunctionField deg placeInfty

The place at infinity of a rational function field has degree one.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_deg_placeInfty
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem _root_.AlgebraicCurve.RationalFunctionField.deg_placeInfty (K : Type*) [Field K]
  [DecidableEq (RatFunc K)] : (placeInfty K).deg = 1 :=
  AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
    (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K)
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_deg_placeInfty
end ProofImplementation

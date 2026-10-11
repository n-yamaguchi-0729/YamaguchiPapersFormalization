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

import Mathlib.FieldTheory.RatFunc.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_degree_eq_zero_of_forall_eq_ord

/-!
# Rational Function Field degree eq zero of is Principal
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_degree_eq_zero_of_isPrincipal
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem _root_.AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_isPrincipal {K : Type*}
  [Field K] {D : Divisor K (RatFunc K)} (hD : D.IsPrincipal) : Divisor.degree D = 0 := by
  obtain ⟨f, -, hDf⟩ := hD
  exact AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord D hDf
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_degree_eq_zero_of_isPrincipal
end ProofImplementation

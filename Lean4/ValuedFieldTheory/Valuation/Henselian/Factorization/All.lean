/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
import ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
import ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
import ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
import ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
import ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds
import ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
import ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
import ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
import ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
import ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
import ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits
import ValuedFieldTheory.Valuation.Henselian.Factorization.Step
import ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation
import ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits

/-!
# Henselian polynomial factorization

The approximation, correction, and completeness results used to lift coprime
factorizations over valuation rings.
-/


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.DVRLocalExtension
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.LocalizationLocalMap
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.LocalizationRing
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.PrimePowerRoots
import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

/-!
# Finite extensions of discrete valuation fields

This aggregate exposes degree and defectlessness, henselianity, localizations, discrete
prolongations, prime-power roots, and uniqueness of extensions.
-/

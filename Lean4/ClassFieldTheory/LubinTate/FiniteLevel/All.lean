/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
import ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
import ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
import ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
import ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
import ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
import ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
import ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
import ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
import ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
import ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
import ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
import ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
import ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
import ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
import ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
import ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
import ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
import ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
import ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
import ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification

/-!
# General finite-level Lubin--Tate theory

Public aggregate for the characteristic-independent standard division
polynomials, primitive torsion fields, analytic formal-module action, explicit
finite Galois parameterization, integral-closure valuation, ramification
filtrations and their Herbrand formula, level-field tower, and the norm of a
primitive uniformizer.  It also exports stability of a standard level under
a principal-unit change of its defining uniformizer.
-/


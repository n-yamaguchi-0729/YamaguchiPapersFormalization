/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian
import ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import ValuedFieldTheory.Valuation.Henselian.AlgebraicIntegralClosure
import ValuedFieldTheory.Valuation.Henselian.Complete
import ValuedFieldTheory.Valuation.Henselian.CoprimeFactorLifting
import ValuedFieldTheory.Valuation.Henselian.Core
import ValuedFieldTheory.Valuation.Henselian.EtaleLifting
import ValuedFieldTheory.Valuation.Henselian.Factorization.All
import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
import ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import ValuedFieldTheory.Valuation.Henselian.NonmonicReduction
import ValuedFieldTheory.Valuation.Henselian.NonmonicSimpleRoot
import ValuedFieldTheory.Valuation.Henselian.NormedGaloisIsometry
import ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization
import ValuedFieldTheory.Valuation.Henselian.PrimitiveReduction
import ValuedFieldTheory.Valuation.Henselian.RingEquiv
import ValuedFieldTheory.Valuation.Henselian.SimpleRootFactorization
import ValuedFieldTheory.Valuation.Henselian.StandardEtaleLifting
import ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions
import ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive
import ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion

import ValuedFieldTheory.Valuation.Henselian.PrincipalUnitRoots

import ValuedFieldTheory.Valuation.Henselian.ArtinSchreier

import ValuedFieldTheory.Valuation.Henselian.RootsOfUnity
import ValuedFieldTheory.Valuation.Henselian.FiniteResidueRootLifting

/-!
# Henselian valuation theory

Public aggregate for the Henselian factorization criterion, polynomial lifting,
and uniqueness results for algebraic valuation extensions.
-/


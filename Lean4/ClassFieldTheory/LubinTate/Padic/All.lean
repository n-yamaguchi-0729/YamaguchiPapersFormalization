/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.All
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
import ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
import ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
import ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed
import ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
import ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
import ClassFieldTheory.LubinTate.Padic.CompletedLevel
import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
import ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
import ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
import ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
import ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed
import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.All
import ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
import ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries

/-!
# P-adic Lubin--Tate theory

Aggregate for the multiplicative Lubin--Tate series and its completed-level,
Frobenius, residue, fixed-field, and changed-uniformizer constructions.
-/


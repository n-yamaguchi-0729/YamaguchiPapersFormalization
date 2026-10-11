/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois

/-!
# Finite Lubin--Tate levels in equal characteristic

Public aggregate for division torsion, finite level fields, and their Galois
and norm structure.
-/


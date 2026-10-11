/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.LocalField.Padic.ClosedAddSubgroup
import ValuedFieldTheory.LocalField.Padic.CompactDenominator
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.All
import ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerCharacter
import ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerRestriction
import ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
import ValuedFieldTheory.LocalField.Padic.PrincipalUnits
import ValuedFieldTheory.LocalField.Padic.PrimePowerTorsionReduction
import ValuedFieldTheory.LocalField.Padic.ReductionCompatibility
import ValuedFieldTheory.LocalField.Padic.ResidueInverseLimit
import ValuedFieldTheory.LocalField.Padic.Teichmuller
import ValuedFieldTheory.LocalField.Padic.TeichmullerReduction
import ValuedFieldTheory.LocalField.Padic.UnitDecomposition
import ValuedFieldTheory.LocalField.Padic.PrimitiveRootTeichmullerCharacter

/-!
# Padic local fields and their units

This aggregate exposes padic local-field structures, cyclotomic extensions, Teichmuller
characters and reduction, and principal-unit comparisons.
-/

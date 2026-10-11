/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
import ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
import ClassFieldTheory.LubinTate.FormalModule.Intertwiner
import ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
import ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
import ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
import ClassFieldTheory.LubinTate.FormalModule.Reduction
import ClassFieldTheory.LubinTate.FormalModule.Series
import ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import ClassFieldTheory.LubinTate.FormalModule.StandardSeries

/-!
# Lubin--Tate formal modules

Public aggregate for the formal-series constructions used by Lubin--Tate
theory: composition, linear terms, intertwiners, coefficient equations,
reduction, the standard Lubin--Tate series, and the coefficientwise recursive
existence-and-uniqueness construction, including the resulting standard
commutative formal group and its coefficient-ring endomorphisms.
-/


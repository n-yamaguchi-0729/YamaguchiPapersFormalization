/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivAdeleTopology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivFiniteIntegral
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange

/-!
# Idelic class groups

Public aggregate for the ordinary ideal class quotient of the ideles and its
base-change, norm-comparison, tower, and algebra-equivalence constructions.
-/


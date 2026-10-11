/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.FiniteMathlibTopologyComparison
import ClassFieldTheory.AlgebraicNumberTheory.Idele.FinitePrime
import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent
import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PositiveArchimedeanSection
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SufficientlyLarge
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology

/-!
# Ideles and idele classes

Public aggregate for the idele group and the idele class group of a number
field.
-/


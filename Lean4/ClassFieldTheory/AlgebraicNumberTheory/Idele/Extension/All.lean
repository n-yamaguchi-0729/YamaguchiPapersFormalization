/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.InfiniteOnePlaceBaseNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm

/-!
# Ideles in finite extensions of number fields

Public aggregate for base change, extension, and norm maps on ideles and
idele classes.
-/


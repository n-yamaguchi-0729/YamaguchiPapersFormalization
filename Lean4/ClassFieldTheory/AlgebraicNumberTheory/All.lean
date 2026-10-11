/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.Adele.All
import ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Completion.All
import ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
import ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
import ClassFieldTheory.AlgebraicNumberTheory.Galois.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.All
import ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
import ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
import ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
import ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import ClassFieldTheory.AlgebraicNumberTheory.TensorProduct

/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/


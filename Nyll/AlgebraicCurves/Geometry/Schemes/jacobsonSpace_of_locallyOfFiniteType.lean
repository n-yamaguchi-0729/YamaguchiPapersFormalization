/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# jacobson Space of locally Of Finite Type
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.jacobsonSpace_of_locallyOfFiniteType

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType
    {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType
      t] :
    JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace t
end AlgebraicCurves.Geometry.Schemes.Proofs.jacobsonSpace_of_locallyOfFiniteType
end ProofImplementation

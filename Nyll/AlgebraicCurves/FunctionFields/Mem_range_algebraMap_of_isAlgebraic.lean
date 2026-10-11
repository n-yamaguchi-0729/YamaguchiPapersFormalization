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

import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Mem range algebra Map of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Mem_range_algebraMap_of_isAlgebraic

theorem _root_.AlgebraicCurve.mem_range_algebraMap_of_isAlgebraic {K L : Type*} [Field K] [Field L]
  [Algebra K L] [IsAlgClosed K] {x : L} (hx : IsAlgebraic K x) :
    x ∈ (algebraMap K L).range :=
  minpoly.degree_eq_one_iff.mp
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx.isIntegral))

end AlgebraicCurves.FunctionFields.Proofs.Mem_range_algebraMap_of_isAlgebraic
end ProofImplementation

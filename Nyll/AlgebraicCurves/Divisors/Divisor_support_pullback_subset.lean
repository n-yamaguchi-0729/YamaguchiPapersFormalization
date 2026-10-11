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

import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.Evaluation

/-!
# Divisor support pullback subset
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_support_pullback_subset

open AlgebraicCurve AlgebraicCurve.Divisor

theorem _root_.AlgebraicCurve.Divisor.support_pullback_subset {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral
  F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')] (E : Divisor K F) :
  (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') := by
  classical
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨w.restrict F,
    restrict_mem_support_of_mem_support_pullback hw, w.restrict_mem_fiber⟩
end AlgebraicCurves.Divisors.Proofs.Divisor_support_pullback_subset
end ProofImplementation

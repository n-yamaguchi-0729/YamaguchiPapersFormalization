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

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Finrank Along id
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FinrankAlong_id

theorem _root_.AlgebraicCurve.finrankAlong_id {K F : Type*} [Field K] [Field F] [Algebra K F] :
    AlgebraicCurve.finrankAlong K (AlgHom.id K F) = 1 := by
  let : Algebra F F := AlgebraicCurve.algebraAlong (AlgHom.id K F)
  change Module.finrank F F = 1
  exact Module.finrank_self F

end AlgebraicCurves.FunctionFields.Proofs.FinrankAlong_id
end ProofImplementation

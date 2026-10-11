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

import AlgebraicCurves.Divisors.Correspondences

/-!
# Finite Along of surjective
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FiniteAlong_of_surjective

open AlgebraicCurve

theorem _root_.AlgebraicCurve.finiteAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field
  F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ
  := by
  let := algebraAlong φ
  exact Module.Finite.of_surjective (Algebra.linearMap F F') hφ
end AlgebraicCurves.FunctionFields.Proofs.FiniteAlong_of_surjective
end ProofImplementation

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
# Finite Along comp
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FiniteAlong_comp

open AlgebraicCurve

theorem _root_.AlgebraicCurve.finiteAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F']
  [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ
  : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by
  let := algebraAlong φ
  let := algebraAlong χ
  let := algebraAlong (χ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite F F' := hφ
  have : Module.Finite F' F'' := hχ
  exact Module.Finite.trans F' F''
end AlgebraicCurves.FunctionFields.Proofs.FiniteAlong_comp
end ProofImplementation

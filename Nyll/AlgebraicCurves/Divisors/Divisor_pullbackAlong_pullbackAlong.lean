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
import Nyll.AlgebraicCurves.Places.Place_restrictAlong_restrictAlong
import Nyll.AlgebraicCurves.Places.Place_ramificationIndexAlong_comp

/-!
# Divisor pullback Along pullback Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_pullbackAlong

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong {K F F' F'' : Type*} [Field K]
  [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ
  : F' →ₐ[K] F'') [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F''] (hφ :
  φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D
  : Divisor K F) : Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) =
  Divisor.pullbackAlong (χ.comp φ) hχφ D := by
  ext W
  rw [Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply,
    AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
    AlgebraicCurve.Place.ramificationIndexAlong_comp φ χ hφ hχ hχφ]
  push_cast
  ring
end AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_pullbackAlong
end ProofImplementation

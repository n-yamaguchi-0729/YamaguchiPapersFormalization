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
# Place restrict Along restrict Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_restrictAlong_restrictAlong

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.restrictAlong_restrictAlong {K F F' F'' : Type*} [Field K]
  [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
  (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp
  φ).toRingHom.IsIntegral) (W : Place K F'') : (W.restrictAlong χ hχ).restrictAlong φ hφ =
  W.restrictAlong (χ.comp φ) hχφ :=
  Place.ext (SetLike.ext fun _ => Iff.rfl)
end AlgebraicCurves.Places.Proofs.Place_restrictAlong_restrictAlong
end ProofImplementation

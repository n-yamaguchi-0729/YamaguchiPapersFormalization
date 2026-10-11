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

import AlgebraicCurves.Differentials.Basic

/-!
# Pullback Diff smul
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.PullbackDiff_smul

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.pullbackDiff_smul {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (g : F) (ω : Ω[F⁄K]) :
    pullbackDiff φ (g • ω) = φ g • pullbackDiff φ ω := by
  let : Algebra F F' := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  change (KaehlerDifferential.map K K F F') (g • ω) = φ g • (KaehlerDifferential.map K K F F') ω
  rw [map_smul]
  exact (algebraMap_smul F' g _).symm
end AlgebraicCurves.Differentials.Proofs.PullbackDiff_smul
end ProofImplementation

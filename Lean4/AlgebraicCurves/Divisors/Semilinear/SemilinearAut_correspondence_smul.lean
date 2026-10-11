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
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pullbackAlong_smul
import AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pushforwardAlong_smul

/-!
# Semilinear Aut correspondence smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g :
  SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ :
  φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hgφ : IntertwinesAlong φ.toRingHom g g')
  (hgψ : IntertwinesAlong ψ.toRingHom g g') (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (g
  • D) = g • Divisor.correspondence φ ψ hφ hψ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    pullbackAlong_smul φ hφ hgφ, pushforwardAlong_smul ψ hψ hgψ]

end

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_correspondence_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.correspondence_smul {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
  [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ :
  ψ.toRingHom.IsIntegral) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong
  ψ.toRingHom g g') (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (g • D) = g •
  Divisor.correspondence φ ψ hφ hψ D := by
  exact
    _root_.AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_correspondence_smul.solution (K
    := K) (F := F) (F' := F') (g := g) (g' := g') (φ := φ) (ψ := ψ) (hφ := hφ) (hψ := hψ) (hgφ :=
    hgφ) (hgψ := hgψ) (D := D)

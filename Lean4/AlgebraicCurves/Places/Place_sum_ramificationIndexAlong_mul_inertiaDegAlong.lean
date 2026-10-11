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
import AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg

/-!
# Place sum ramification Index Along mul inertia Deg Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndexAlong_mul_inertiaDegAlong

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ :
  φ.toRingHom.IsIntegral) [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep :
  SeparableAlong K φ) (v : Place K F) : ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ
  : ℤ) * (w.inertiaDegAlong φ hφ : ℤ) = (finrankAlong K φ : ℤ) := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  exact Place.sum_ramificationIndex_mul_inertiaDeg v

end
end AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
end ProofImplementation

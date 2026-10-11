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
# Divisor correspondence single
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Divisor.correspondence_single {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ :
  φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F) (n : ℤ) :
  Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = ∑ w ∈ Place.fiberAlong φ hφ v,
  Finsupp.single (w.restrictAlong ψ hψ) (n * (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong
  ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
  exact Finset.sum_congr rfl fun w _ => Divisor.pushforwardAlong_single ψ hψ w _

end
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single
end ProofImplementation

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
import AlgebraicCurves.Divisors.Divisor_correspondence_single

/-!
# Divisor correspondence single of forall restrict Along eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_of_forall_restrictAlong_eq

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Divisor.correspondence_single_of_forall_restrictAlong_eq {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ
  ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (v : Place K F)
  (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v, w.restrictAlong ψ hψ = v) (n : ℤ) :
  Divisor.correspondence φ ψ hφ hψ (Finsupp.single v n) = Finsupp.single v (n * ∑ w ∈
  Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong ψ hψ : ℤ)) := by
  rw [Divisor.correspondence_single φ ψ hφ hψ v n, Finset.mul_sum, Finsupp.single_finsetSum]
  exact Finset.sum_congr rfl fun w hw => by rw [hcoll w hw, mul_assoc]

end
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_of_forall_restrictAlong_eq
end ProofImplementation

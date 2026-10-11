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
import Nyll.AlgebraicCurves.Divisors.Divisor_correspondence_single_of_forall_restrictAlong_eq
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndexAlong_mul_inertiaDegAlong

/-!
# Divisor correspondence single eq finrank Along smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_eq_finrankAlong_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem _root_.AlgebraicCurve.Divisor.correspondence_single_eq_finrankAlong_smul {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F
  →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
  (hsep : SeparableAlong K φ) (v : Place K F) (hcoll : ∀ w ∈ Place.fiberAlong φ hφ v,
  w.restrictAlong ψ hψ = v) (hfψ : ∀ w ∈ Place.fiberAlong φ hφ v, w.inertiaDegAlong ψ hψ = 1) (hfφ
  : ∀ w ∈ Place.fiberAlong φ hφ v, w.inertiaDegAlong φ hφ = 1) (n : ℤ) : Divisor.correspondence φ ψ
  hφ hψ (Finsupp.single v n) = (finrankAlong K φ : ℤ) • Finsupp.single v n := by
  rw [Divisor.correspondence_single_of_forall_restrictAlong_eq φ ψ hφ hψ v hcoll n,
    Finsupp.smul_single,
    smul_eq_mul, mul_comm (finrankAlong K φ : ℤ) n]
  congr 1
  rw [← Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep v]
  congr 1
  exact Finset.sum_congr rfl fun w hw => by rw [hfψ w hw, hfφ w hw]

end
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_single_eq_finrankAlong_smul
end ProofImplementation

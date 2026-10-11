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

import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforwardNormFormula_of_isSeparable

/-!
# Place ord norm eq zero of forall fiber of is Separable
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_norm_eq_zero_of_forall_fiber_of_isSeparable

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber_of_isSeparable {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower
  K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'}
  (hf : f ≠ 0) (v : Place K F) (h : ∀ w ∈ v.fiber F', w.ord f = 0) : v.ord (Algebra.norm F f) = 0
  := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  rw [← AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable f hf D hD v,
    Divisor.pushforward_apply]
  refine Finset.sum_eq_zero fun w hw => ?_
  split_ifs with hwv
  · rw [hD w, h w (Place.mem_fiber.mpr hwv), zero_mul]
  · rfl
end AlgebraicCurves.Places.Proofs.Place_ord_norm_eq_zero_of_forall_fiber_of_isSeparable
end ProofImplementation

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

import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg
import Nyll.AlgebraicCurves.Places.Place_inertiaDeg_eq_one_of_isRational

/-!
# Place sum ramification Index eq finrank
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_eq_finrank

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] (v : Place K F)
  (hv : v.IsRational) (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) : ∑ w ∈ v.fiber F',
  (w.ramificationIndex F : ℤ) = (Module.finrank F F' : ℤ) := by
  rw [← AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg (F' := F') v]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [w.inertiaDeg_eq_one_of_isRational (hrat w hw)
    ((Place.mem_fiber.mp hw).symm ▸ hv), Nat.cast_one, mul_one]
end AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_eq_finrank
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Maps

/-!
# Sum Ramification Inertia of fundamental Identity
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.SumRamificationInertia_of_fundamentalIdentity

open AlgebraicCurve

theorem _root_.AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']
    [FundamentalIdentity K F F']
    (hdeg : ∀ v : Place K F, v.deg ≠ 0) : SumRamificationInertia K F F' := by
  refine ⟨fun v => ?_⟩
  have key := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') v
  have hsum : ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (v.deg : ℤ) * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← Place.deg_restrict_mul_inertiaDeg (F := F) w, Place.mem_fiber.mp hw]
    push_cast
    ring
  have hv : (v.deg : ℤ) ≠ 0 := by exact_mod_cast hdeg v
  apply mul_left_cancel₀ hv
  rw [← hsum, key, mul_comm]

end AlgebraicCurves.Places.Proofs.SumRamificationInertia_of_fundamentalIdentity
end ProofImplementation

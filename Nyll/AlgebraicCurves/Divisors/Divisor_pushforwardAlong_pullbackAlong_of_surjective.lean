/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Nyll.AlgebraicCurves.FunctionFields.FiniteAlong_of_surjective

/-!
# Divisor pushforward Along pullback Along of surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_pullbackAlong_of_surjective

open _root_.AlgebraicCurve

section Helpers

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem separableAlong_of_surjective_aux (φ : F →ₐ[K] F') (hs : Function.Surjective φ) :
    SeparableAlong K φ := by
  let := algebraAlong φ
  exact ⟨fun x => by
    obtain ⟨a, rfl⟩ := hs x
    exact isSeparable_algebraMap (K := F') a⟩

private theorem finrankAlong_eq_one_of_surjective_aux (φ : F →ₐ[K] F') (hs : Function.Surjective φ)
  :
    finrankAlong K φ = 1 := by
  let := algebraAlong φ
  change Module.finrank F F' = 1
  have e : F ≃ₗ[F] F' :=
    LinearEquiv.ofBijective (Algebra.linearMap F F') ⟨(algebraMap F F').injective, hs⟩
  rw [← e.finrank_eq, Module.finrank_self]

end Helpers

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Divisor
open _root_.AlgebraicCurve.Divisor
end AlgebraicCurve.Divisor
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Divisor in
private theorem AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective_aux {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ
  : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D :
  AlgebraicCurve.Divisor K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ
  (AlgebraicCurve.Divisor.pullbackAlong φ hφ D) = D := by
  have hsum := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ (finiteAlong_of_surjective
    φ hs)
    (separableAlong_of_surjective_aux φ hs)
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single v n =>
    rw [Divisor.pullbackAlong_single, map_sum]
    have hv := hsum v
    rw [finrankAlong_eq_one_of_surjective_aux φ hs, Nat.cast_one] at hv
    calc ∑ W ∈ Place.fiberAlong φ hφ v,
          Divisor.pushforwardAlong φ hφ (Finsupp.single W (n * (W.ramificationIndexAlong φ : ℤ)))
        = ∑ W ∈ Place.fiberAlong φ hφ v,
            Finsupp.single v (n * ((W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong φ hφ :
              ℤ))) := by
          refine Finset.sum_congr rfl fun W hW => ?_
          rw [Divisor.pushforwardAlong_single, Place.mem_fiberAlong.mp hW, mul_assoc]
      _ = Finsupp.single v n := by
          rw [← Finsupp.single_finsetSum, ← Finset.mul_sum, hv, mul_one]

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F
  →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D : AlgebraicCurve.Divisor
  K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ (AlgebraicCurve.Divisor.pullbackAlong φ hφ D)
  = D :=
  AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective_aux φ hφ hs D

end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_pullbackAlong_of_surjective
end ProofImplementation

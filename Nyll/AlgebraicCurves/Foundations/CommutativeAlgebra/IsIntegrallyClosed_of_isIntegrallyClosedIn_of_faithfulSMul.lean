/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Is Integrally Closed of is Integrally Closed In of faithful SMul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul

theorem _root_.IsIntegrallyClosed.of_isIntegrallyClosedIn_of_faithfulSMul
    (A F : Type*) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [FaithfulSMul A F]
    [IsIntegrallyClosedIn A F] : IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  have hinj : Function.Injective (algebraMap A F) := FaithfulSMul.algebraMap_injective A F
  let φ : FractionRing A →ₐ[A] F :=
    { IsFractionRing.lift hinj with
      commutes' := fun a => by simp [IsFractionRing.lift_algebraMap] }
  have hφ : ∀ y, φ y = IsFractionRing.lift hinj y := fun _ => rfl
  have hx' : IsIntegral A (φ x) := hx.map φ
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hx'
  refine ⟨a, ?_⟩
  apply (IsFractionRing.lift hinj : FractionRing A →+* F).injective
  rw [IsFractionRing.lift_algebraMap, ← hφ]
  exact ha
end IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

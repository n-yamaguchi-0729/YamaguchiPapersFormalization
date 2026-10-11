/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

/-!
# Is Integrally Closed mem minimal Primes of mem associated Primes
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes

theorem _root_.IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ associatedPrimes A (A ⧸ Ideal.span {x})) : P ∈ (Ideal.span {x}).minimalPrimes := by
  have h1 : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hx P hP
  have hle : Ideal.span {x} ≤ P := by
    have h := (show IsAssociatedPrime P (A ⧸ Ideal.span {x}) from hP).annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h
  have hbelow : ∀ q : Ideal A, q.IsPrime → q < P → q = ⊥ := by
    intro q hq hlt
    have := hq
    have hPle : P.height ≤ ((1 : ℕ) : ℕ∞) := by rw [h1]; norm_cast
    have hlt1 : q.height < ((1 : ℕ) : ℕ∞) := (Ideal.height_le_iff.mp hPle) q hq hlt
    have h0 : q.height = 0 := by
      apply Order.lt_one_iff.mp
      exact_mod_cast hlt1
    have hmin : q ∈ (⊥ : Ideal A).minimalPrimes := Ideal.height_eq_zero_iff.mp h0
    simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hmin
  refine ⟨⟨‹P.IsPrime›, hle⟩, fun q hq hqP => ?_⟩
  rcases lt_or_eq_of_le hqP with hlt | rfl
  · exfalso
    have hqbot := hbelow q hq.1 hlt
    apply hx
    have hxq : x ∈ q := hq.2 (Ideal.subset_span rfl)
    simpa [hqbot] using hxq
  · exact le_rfl
end IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

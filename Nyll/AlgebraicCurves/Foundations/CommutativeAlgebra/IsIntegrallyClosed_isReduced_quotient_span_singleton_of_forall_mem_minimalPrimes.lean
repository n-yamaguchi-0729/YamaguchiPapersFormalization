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

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsIntegrallyClosed_mem_minimalPrimes_of_mem_associatedPrimes
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes

/-!
# Is Integrally Closed is Reduced quotient span singleton of forall mem minimal Primes
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes

theorem _root_.IsIntegrallyClosed.isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {x : A} (hx : x ≠ 0)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ (Ideal.span {x}).minimalPrimes →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) :=
  Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes x fun P _ hP =>
    h P (IsIntegrallyClosed.mem_minimalPrimes_of_mem_associatedPrimes hx P hP)
end IsIntegrallyClosed_isReduced_quotient_span_singleton_of_forall_mem_minimalPrimes
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

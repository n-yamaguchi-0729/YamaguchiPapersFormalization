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

import Nyll.AlgebraicCurves.Valuations.IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
import Nyll.AlgebraicCurves.Valuations.Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

/-!
# Is Integrally Closed height eq one of mem associated Primes
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

theorem _root_.IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1 :=
  Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime P
    (IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes hx P hP)
end IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

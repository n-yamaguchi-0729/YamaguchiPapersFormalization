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

import AlgebraicCurves.Valuations.ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import AlgebraicCurves.Divisors.ClassGroup

/-!
# Place exists of valuation Subring of finite Dimensional
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_of_valuationSubring_of_finiteDimensional

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A :=
  ⟨⟨A, hAK, hA, ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x A hAK hA⟩, rfl⟩

end AlgebraicCurves.Places.Proofs.Place_exists_of_valuationSubring_of_finiteDimensional
end ProofImplementation

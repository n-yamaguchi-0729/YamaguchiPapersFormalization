/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentFundamentalGroupQuotients
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentQuotientsEveryOrder
import Nyll.ProCGroups.Completion.ProfiniteIntegerRecognition
import Nyll.ProCGroups.Completion.ProCInteger
import Nyll.ProCGroups.Generation.Basic

/-!
# The actual fundamental group of the multiplicative line

The finite-etale geometry supplies both a topological generator and actual quotients of every
positive order. The normalized-coefficient construction identifies the fibre-functor
automorphism group, with its original topology, with the inverse limit of all finite cyclic
groups. The isomorphism depends on the choice of topological generator.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

open ProCGroups ProCGroups.Completion

/-- Over an algebraically closed characteristic-zero field, the actual etale fundamental group
of the multiplicative line is the full profinite integer group. The displayed generator and
isomorphism are constructed, not supplied as comparison data. -/
theorem exists_fundamentalGroup_laurent_profiniteInteger_equiv
    {K Ω : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ Spec (.of (LaurentPolynomial K))) :
    ∃ (g : π₁ᵉᵗ(ξ))
      (e : π₁ᵉᵗ(ξ) ≃ₜ* Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.allFinite : FiniteGroupClass.{0}))),
      Generation.TopologicallyGenerates ({g} : Set π₁ᵉᵗ(ξ)) ∧
      e g = proCIntegerOne (C := FiniteGroupClass.allFinite) := by
  obtain ⟨g, hg⟩ := exists_topological_generator_fundamentalGroup_laurent ξ
  have orders : ∀ n : ℕ, 0 < n → ∃ U : OpenNormalSubgroup π₁ᵉᵗ(ξ),
      Nat.card (π₁ᵉᵗ(ξ) ⧸ (U : Subgroup π₁ᵉᵗ(ξ))) = n := by
    intro n hn
    obtain ⟨U, _, hU⟩ := exists_openNormalQuotient_fundamentalGroup_laurent_card ξ hn
    exact ⟨U, hU⟩
  obtain ⟨e, he⟩ := exists_profiniteInteger_equiv_of_generator_and_quotient_orders g hg orders
  exact ⟨g, e, hg, he⟩

end AnabelianGeometry.GeometricFundamentalGroup

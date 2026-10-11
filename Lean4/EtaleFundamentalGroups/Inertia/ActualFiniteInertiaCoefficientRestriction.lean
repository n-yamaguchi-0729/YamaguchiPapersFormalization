/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationInclusionSquare
import SchemeTheory.RingTheory.Ramification.InertiaCoefficientContraction

/-!
# Inertia under finite coefficient restriction

Transfers the ambient normalization inertia difference condition to the contracted finite
normalization prime through the coefficient inclusion square.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Restriction of an actual ambient normalization inertia automorphism
satisfies the inertia condition at the literal finite contraction. The
coefficient square is proved by the actual restriction construction. -/
theorem actualFiniteNormalizationRestriction_inertia_difference
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L))
    (E : FiniteGaloisIntermediateField K L) (σ : Gal(L/K))
    (hσ : ∀ b : normalizationCommAlgCat A L,
      normalizationGaloisRingHom A K L σ b - b ∈ Q) :
    ∀ b : finiteAbsoluteNormalizationAlgebra A K L E,
      actualFiniteNormalizationRestrictionRingHom A K L E σ b - b ∈
        finiteAbsoluteNormalizationPrime A K L Q E :=
  inertiaDifference_comap_of_coefficient_square
    (finiteAbsoluteNormalizationRingMap A K L E)
    (actualFiniteNormalizationRestrictionRingHom A K L E σ)
    (normalizationGaloisRingHom A K L σ) Q
    (actualFiniteNormalizationRestrictionRingHom_inclusion A K L E σ) hσ

end EtaleFundamentalGroups.Inertia

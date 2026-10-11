/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaCoefficientRestriction

/-!
# Original inertia at finite normalization primes

Proves the coefficient difference condition for restriction of original inertia to the
contracted finite normalization prime.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every element of the original actual inertia restricts to inertia at
the literal finite normalization prime. The finite action and its square
are constructed from actual restriction, with no comparison premise. -/
theorem originalInertia_finiteNormalization_difference
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L)) (E : FiniteGaloisIntermediateField K L)
    (σ : actualNormalizationInertiaGroup A K L Q) :
    ∀ b : finiteAbsoluteNormalizationAlgebra A K L E,
      (finiteAbsoluteNormalizationPrime A K L Q E).carrier
        ((actualFiniteNormalizationRestrictionRingHom A K L E
          (actualNormalizationInertiaElement A K L Q σ)).toFun b - b) :=
  actualFiniteNormalizationRestriction_inertia_difference A K L Q E
    (actualNormalizationInertiaElement A K L Q σ)
    (actualNormalizationInertia_difference A K L Q σ)

end EtaleFundamentalGroups.Inertia

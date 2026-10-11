/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameCoordinate
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameContinuity

/-!
# Surjectivity and local constancy of the finite quotient coordinate

The proved original finite-coordinate properties are preserved by the SAME
canonical quotient comparison. Its root carriers and coefficient dictionaries
remain inside their existing single-stage owners.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
  (E : FiniteGaloisIntermediateField K L)

/-- The actual finite quotient coordinate is onto. -/
theorem actualFiniteQuotientTameCoordinate_surjective :
    Function.Surjective (actualFiniteQuotientTameCoordinate A K L Q E).toFun :=
  (normalizationQuotientRootsEquiv A L Q
    (actualFiniteStageTameOrder A K L Q E)).toEquiv.surjective.comp
      (actualFiniteTameCoordinate_surjective A K L Q E)

/-- The SAME finite quotient coordinate is locally constant in the
original Krull subgroup topology. -/
theorem actualFiniteQuotientTameCoordinate_isLocallyConstant :
    IsLocallyConstant (actualFiniteQuotientTameCoordinate A K L Q E).toFun :=
  (actualFiniteTameCoordinate_isLocallyConstant A K L Q E).comp
    (normalizationQuotientRootsEquiv A L Q
      (actualFiniteStageTameOrder A K L Q E)).toEquiv.toFun

end EtaleFundamentalGroups.Inertia

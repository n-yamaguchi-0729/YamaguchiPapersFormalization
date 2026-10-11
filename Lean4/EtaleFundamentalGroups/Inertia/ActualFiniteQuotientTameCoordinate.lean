/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.NormalizationQuotientRoots

/-!
# The original finite coordinate in the literal quotient

This single-stage owner applies the SAME canonical maximal quotient/residue
comparison before a second degree or a finite-stage ordering is introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

/-- The SAME finite canonical coordinate, in the literal quotient root group. -/
def actualFiniteQuotientTameCoordinate
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    (actualNormalizationInertiaGroup A K L Q).carrier →*
      rootsOfUnity (actualFiniteStageTameOrder A K L Q E)
        ((normalizationCommAlgCat A L).carrier ⧸ Q) :=
  (normalizationQuotientRootsEquiv A L Q
    (actualFiniteStageTameOrder A K L Q E)).toMonoidHom.comp
      (actualFiniteTameCoordinate A K L Q E).hom'

end EtaleFundamentalGroups.Inertia

end

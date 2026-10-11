/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeCanonicalTameScalarData
import EtaleFundamentalGroups.Inertia.ActualFiniteResidueAction
import EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms

/-!
# The canonical scalar action at the actual finite normalization

The factory closes the finite root interface before original inertia and
decomposition elements occur. Every field is the already constructed map.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The SAME normalized finite scalar character, conjugation and residue action. -/
def actualFiniteTameScalarData (E : FiniteGaloisIntermediateField K L) :
    ScalarInertiaActionData.{w} := by
  have : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsMaximal :=
    actualFiniteNormalizationPrime_isMaximal A K L Q E
  exact commAlgCanonicalTameScalarData A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- Equivariance is an independently proved theorem about those actual data. -/
theorem actualFiniteTameScalarData_equivariant
    (E : FiniteGaloisIntermediateField K L)
    (d : (actualFiniteTameScalarData A K L Q E).decomposition)
    (σ : (actualFiniteTameScalarData A K L Q E).inertia) :
    (actualFiniteTameScalarData A K L Q E).character
        ((actualFiniteTameScalarData A K L Q E).conjugate d σ) =
      (actualFiniteTameScalarData A K L Q E).action d
        ((actualFiniteTameScalarData A K L Q E).character σ) := by
  have : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsMaximal :=
    actualFiniteNormalizationPrime_isMaximal A K L Q E
  exact commAlgCanonicalTameScalarData_equivariant A
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E) d σ

end EtaleFundamentalGroups.Inertia

end

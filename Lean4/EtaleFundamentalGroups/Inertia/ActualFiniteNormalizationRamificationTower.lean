/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import SchemeTheory.Normalization.SubalgebraNormalizationTowerRamification

/-!
# Ramification indices in finite normalization towers

Proves the multiplicative tower identity for ramification indices using the algebra structure
induced by the finite normalization inclusion.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The actual finite-normalization ramification indices satisfy the tower
identity. The relative algebra is exactly the existing literal inclusion;
all Dedekind, scalar-tower, and flatness facts come from the original data. -/
theorem actualFiniteNormalization_ramificationIdx_tower
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDedekindDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L))
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    letI : Algebra (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationAlgebra A K L F) :=
      (actualFiniteNormalizationTowerRingMap A K L E F h).toAlgebra
    (finiteAbsoluteNormalizationPrime A K L Q F).ramificationIdx A =
      (finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A *
        (finiteAbsoluteNormalizationPrime A K L Q F).ramificationIdx
          (finiteAbsoluteNormalizationAlgebra A K L E) := by
  have : IsDedekindDomain
      (subalgebraNormalizationCommAlgCat (finiteLevelNormalizationSubalgebra A K L E)) :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have : IsDedekindDomain
      (subalgebraNormalizationCommAlgCat (finiteLevelNormalizationSubalgebra A K L F)) :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
  exact subalgebraNormalization_ramificationIdx_tower
    (finiteLevelNormalizationSubalgebra A K L E)
    (finiteLevelNormalizationSubalgebra A K L F) h
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime A K L Q F)
    (actualFiniteNormalizationPrime_tower A K L Q E F h)

end EtaleFundamentalGroups.Inertia

end

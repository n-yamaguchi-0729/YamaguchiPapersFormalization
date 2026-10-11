/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteLevelNormalizationAlgebra
import SchemeTheory.Normalization.SubalgebraNormalizationTower
import Mathlib.RingTheory.Ideal.Maps

/-!
# Inclusions of finite normalizations

Constructs injective ring maps between nested finite normalizations. Proves their ambient
inclusion triangle and the contraction identity for chosen primes.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The literal map between the normalizations of two actual finite levels. -/
def actualFiniteNormalizationTowerRingMap
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    finiteAbsoluteNormalizationAlgebra A K L E →+*
      finiteAbsoluteNormalizationAlgebra A K L F :=
  subalgebraNormalizationTowerRingMap
    (finiteLevelNormalizationSubalgebra A K L E)
    (finiteLevelNormalizationSubalgebra A K L F) h

/-- The actual finite normalization inclusions form their literal tower triangle. -/
theorem actualFiniteNormalizationTowerRingMap_comp
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    (finiteAbsoluteNormalizationRingMap A K L F).comp
        (actualFiniteNormalizationTowerRingMap A K L E F h) =
      finiteAbsoluteNormalizationRingMap A K L E :=
  subalgebraNormalizationTowerRingMap_comp
    (finiteLevelNormalizationSubalgebra A K L E)
    (finiteLevelNormalizationSubalgebra A K L F) h

/-- The actual finite tower inclusion is injective. -/
theorem actualFiniteNormalizationTowerRingMap_injective
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    Function.Injective (actualFiniteNormalizationTowerRingMap A K L E F h).toFun :=
  subalgebraNormalizationTowerRingMap_injective
    (finiteLevelNormalizationSubalgebra A K L E)
    (finiteLevelNormalizationSubalgebra A K L F) h

/-- The chosen finite primes are the literal contractions along the tower. -/
theorem actualFiniteNormalizationPrime_tower
    (Q : Ideal (normalizationCommAlgCat A L))
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    finiteAbsoluteNormalizationPrime A K L Q E =
      (finiteAbsoluteNormalizationPrime A K L Q F).comap
        (actualFiniteNormalizationTowerRingMap A K L E F h) := by
  change Q.comap (finiteAbsoluteNormalizationRingMap A K L E) =
    (Q.comap (finiteAbsoluteNormalizationRingMap A K L F)).comap
      (actualFiniteNormalizationTowerRingMap A K L E F h)
  rw [Ideal.comap_comap, actualFiniteNormalizationTowerRingMap_comp]

end EtaleFundamentalGroups.Inertia

end

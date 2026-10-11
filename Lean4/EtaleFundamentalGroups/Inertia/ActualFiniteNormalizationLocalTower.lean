/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import SchemeTheory.RingTheory.Localization.PrimeLocalizationInjection
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local maps in finite normalization towers

Constructs the local ring map at nested finite normalization primes and establishes its
injectivity under the DVR and Galois hypotheses.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]

/-- The literal local ring map at two nested actual finite primes. -/
def actualFiniteNormalizationTowerLocalRingMap
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
    Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) →+*
      Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q F) := by
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  exact Localization.localRingHom
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime A K L Q F)
    (actualFiniteNormalizationTowerRingMap A K L E F h)
    (actualFiniteNormalizationPrime_tower A K L Q E F h)

/-- The actual map of finite local normalizations is injective. -/
theorem actualFiniteNormalizationTowerLocalRingMap_injective
    [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] [IsGalois K L]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    Function.Injective (actualFiniteNormalizationTowerLocalRingMap A K L Q E F h).toFun := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  let := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L F
  exact localRingHom_injective
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime A K L Q F)
    (actualFiniteNormalizationTowerRingMap A K L E F h)
    (actualFiniteNormalizationPrime_tower A K L Q E F h)
    (actualFiniteNormalizationTowerRingMap_injective A K L E F h)

end EtaleFundamentalGroups.Inertia

end

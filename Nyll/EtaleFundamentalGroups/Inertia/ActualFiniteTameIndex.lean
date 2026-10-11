/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationTameProperties
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Finite tame degrees as roots-system indices

Proves positivity and base-ring invertibility of the finite tame degree, and uses them to
construct an index of the canonical roots system.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- Positivity of the degree at the original chosen prime. -/
theorem actualFiniteStageTameOrder_pos (E : FiniteGaloisIntermediateField K L) :
    0 < actualFiniteStageTameOrder A K L Q E := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact finiteNormalizationTameOrder_pos A K L E
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- Invertibility of that actual degree in the original DVR. -/
theorem actualFiniteStageTameOrder_isUnit (E : FiniteGaloisIntermediateField K L) :
    IsUnit (actualFiniteStageTameOrder A K L Q E : A) := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact finiteNormalizationTameOrder_isUnit A K L E
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The actual finite tame degree as an index of the canonical base-residue
roots system. Its invertibility has been proved from the original data. -/
def actualFiniteStageTameIndex (E : FiniteGaloisIntermediateField K L) :
    InvertibleExponent (IsLocalRing.ResidueField A) :=
  ⟨actualFiniteStageTameOrder A K L Q E, by
    simpa only [map_natCast] using
      (actualFiniteStageTameOrder_isUnit A K L Q E).map (IsLocalRing.residue A)⟩

end EtaleFundamentalGroups.Inertia

end

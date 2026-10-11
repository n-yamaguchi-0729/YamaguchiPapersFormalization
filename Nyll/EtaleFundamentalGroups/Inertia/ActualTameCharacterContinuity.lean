/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameProperties
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuity of the actual tame character

The original finite coordinates are locally constant in the original Krull
subgroup topology. Their quotient-valued, degree-indexed coordinates retain
local constancy, so the constructed map into the literal root limit is continuous.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The actual-degree coordinate retains local constancy for the SAME
original inertia topology. -/
theorem actualTameCoordinate_isLocallyConstant
    (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    IsLocallyConstant (actualTameCoordinate A K L Q n).toFun :=
  (actualFiniteQuotientTameCoordinate_isLocallyConstant A K L Q n.property.choose).comp
    (rootsOfUnityDegreeEquiv ((normalizationCommAlgCat A L).carrier ⧸ Q)
      (congrArg Subtype.val n.property.choose_spec)).toEquiv.toFun

/-- Every actual-degree coordinate is continuous for the topology of
its literal stage in the existing root system. -/
theorem actualTameCoordinate_continuous
    (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    Continuous (show (actualNormalizationInertiaGroup A K L Q).carrier →
      (actualFiniteTameRootsSystem A K L Q).X n from
        (actualTameCoordinate A K L Q n).toFun) :=
  IsLocallyConstant.continuous
    (Y := (actualFiniteTameRootsSystem A K L Q).X n)
    (actualTameCoordinate_isLocallyConstant A K L Q n)

/-- The actual canonical character is continuous from original inertia
with its Krull subgroup topology into the literal quotient-root limit. -/
theorem actualTameCharacter_continuous :
    Continuous (actualTameCharacter A K L Q).toFun := by
  exact (actualFiniteTameRootsSystem A K L Q).continuous_inverseLimitLift
    (fun n => (actualTameCoordinate A K L Q n).toFun)
    (actualTameCoordinate_continuous A K L Q)
    (actualTameCoordinate_compatible A K L Q)

end EtaleFundamentalGroups.Inertia

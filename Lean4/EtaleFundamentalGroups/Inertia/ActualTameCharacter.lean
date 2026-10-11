/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameCoordinateCompatibility
import EtaleFundamentalGroups.Inertia.ActualTameRootsGroupSystem

/-!
# The actual canonical tame character

Constructs the group homomorphism from the original inertia into the literal
inverse limit of roots in the original normalization quotient. Evaluation
at a degree is the stage-independent actual canonical finite coordinate.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups.InverseSystems

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The canonical character into the SAME literal quotient-root limit. -/
def actualTameCharacter :
    (actualNormalizationInertiaGroup A K L Q).carrier →*
      (actualFiniteTameRootsSystem A K L Q).inverseLimit where
  toFun := (actualFiniteTameRootsSystem A K L Q).inverseLimitLift
    (fun n => (actualTameCoordinate A K L Q n).toFun)
    (actualTameCoordinate_compatible A K L Q)
  map_one' := by
    apply (actualFiniteTameRootsSystem A K L Q).ext
    intro n
    exact (actualTameCoordinate A K L Q n).map_one'
  map_mul' σ τ := by
    apply (actualFiniteTameRootsSystem A K L Q).ext
    intro n
    exact (actualTameCoordinate A K L Q n).map_mul' σ τ

/-- Evaluation of the actual character is the proved canonical coordinate. -/
theorem actualTameCharacter_projection
    (n : actualFiniteTameDegreeSet A K L Q)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualFiniteTameRootsSystem A K L Q).projection n
        ((actualTameCharacter A K L Q).toFun σ) =
      (actualTameCoordinate A K L Q n).toFun σ := rfl

end EtaleFundamentalGroups.Inertia

end

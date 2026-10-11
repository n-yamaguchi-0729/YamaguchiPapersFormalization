/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameCharacterContinuity
import EtaleFundamentalGroups.Inertia.ActualTameCoordinateSurjectivity
import EtaleFundamentalGroups.Inertia.ActualFiniteTameDegreeDirected
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
import ProCGroups.InverseSystems.CompatibilityAndSurjectivity

/-!
# Surjectivity of the actual tame character

Compactness of the SAME original inertia, local constancy of the actual
coordinates, their proved surjectivity, and directedness of the literal
actual degree range supply the existing compact-limit theorem.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

/-- Every compatible family of actual-degree roots is the canonical tame
character of an original inertia element. No compactness, continuity,
comparison, coordinate-surjectivity or directedness premise is supplied. -/
theorem actualTameCharacter_surjective
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal] :
    Function.Surjective (actualTameCharacter A K L Q).toFun := by
  have : CompactSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
    actualNormalizationInertia_compactSpace A K L Q
  have actualDegrees_nonempty :=
    (actualFiniteTameDegreeSet_nonempty A K L Q).to_subtype
  have : ∀ n : Subtype (actualFiniteTameDegreeSet A K L Q),
      T2Space ((actualFiniteTameRootsSystem A K L Q).X n) := by
    intro n
    have : DiscreteTopology ((actualFiniteTameRootsSystem A K L Q).X n) := ⟨rfl⟩
    infer_instance
  exact (actualFiniteTameRootsSystem A K L Q).surjective_inverseLimitLift
    (fun n => (actualTameCoordinate A K L Q n).toFun)
    (actualTameCoordinate_continuous A K L Q)
    (actualTameCoordinate_compatible A K L Q)
    (actualTameCoordinate_surjective A K L Q)
    (actualFiniteTameDegreeSet_directed A K L Q)

end EtaleFundamentalGroups.Inertia

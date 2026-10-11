/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameCharacter
import EtaleFundamentalGroups.Inertia.ActualTameCoordinateIdentity

/-!
# Detecting the actual character kernel by its original finite coordinates

The canonical quotient comparison preserves and reflects the identity.
Consequently the constructed global character is trivial exactly when all
of the SAME original finite canonical coordinates are trivial.
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

/-- Identity in the actual root limit is detected by all of the original
finite canonical coordinates, without changing their groups or characters. -/
theorem actualTameCharacter_eq_one_iff
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualTameCharacter A K L Q).toFun σ = 1 ↔
      ∀ E : FiniteGaloisIntermediateField K L,
        (actualFiniteTameCoordinate A K L Q E).hom'.toFun σ = 1 := by
  constructor
  · intro h E
    let n : Subtype (actualFiniteTameDegreeSet A K L Q) :=
      ⟨actualFiniteStageTameIndex A K L Q E, E, rfl⟩
    have hproj := congrArg ((actualFiniteTameRootsSystem A K L Q).projection n) h
    change (actualTameCoordinate A K L Q n).toFun σ = 1 at hproj
    exact (actualTameCoordinate_eq_one_iff A K L Q n E rfl σ).mp hproj
  · intro h
    apply (actualFiniteTameRootsSystem A K L Q).ext
    intro n
    change (actualTameCoordinate A K L Q n).toFun σ = 1
    exact (actualTameCoordinate_eq_one_iff A K L Q n n.property.choose
      n.property.choose_spec σ).mpr (h n.property.choose)

end EtaleFundamentalGroups.Inertia

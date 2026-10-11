/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteTameSurjectivity
import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameProperties
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Surjective actual-degree coordinates and primitive roots

The proved original finite-coordinate surjection is transported by the SAME
canonical quotient comparison. Actual finite primitive roots are transported
by that comparison as well. No root-existence or surjectivity is assumed.
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

/-- Every actual-degree coordinate is onto the full root group in the
literal normalization quotient. -/
theorem actualTameCoordinate_surjective
    (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    Function.Surjective (actualTameCoordinate A K L Q n).toFun :=
  (rootsOfUnityDegreeEquiv ((normalizationCommAlgCat A L).carrier ⧸ Q)
    (congrArg Subtype.val n.property.choose_spec)).toEquiv.surjective.comp
      (actualFiniteQuotientTameCoordinate_surjective A K L Q n.property.choose)

/-- Each degree in the literal actual range has a primitive root in the
SAME literal normalization quotient. -/
theorem actualFiniteTameDegreeSet_exists_primitiveRoot
    (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    ∃ ζ : (normalizationCommAlgCat A L).carrier ⧸ Q, IsPrimitiveRoot ζ n.val.val := by
  obtain ⟨E, hE⟩ := n.property
  obtain ⟨ζ, hζ⟩ := actualFiniteStageTameOrder_exists_primitiveRoot A K L Q E
  refine ⟨(normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun ζ, ?_⟩
  have hn : actualFiniteStageTameOrder A K L Q E = n.val.val := congrArg Subtype.val hE
  rw [← hn]
  exact hζ.map_of_injective (normalizationMaximalQuotientResidueEquiv A L Q).symm.injective

end EtaleFundamentalGroups.Inertia

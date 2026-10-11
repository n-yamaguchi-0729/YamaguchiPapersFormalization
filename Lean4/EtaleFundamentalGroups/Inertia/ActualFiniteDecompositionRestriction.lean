/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgDecompositionGroup
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationDecomposition
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationInclusionSquare
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import SchemeTheory.Normalization.AmbientNormalizationGroupMap
import SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# Actual original-to-finite decomposition restriction

The existing original coefficient decomposition morphism fixes the upper
prime. Its literal normalization inclusion square then fixes the contracted
finite prime. These proved facts construct the actual finite restriction.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The existing original decomposition morphism fixes the literal upper
prime under its already identified coefficient ring map. -/
theorem originalNormalizationDecomposition_comap
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (σ : (normalizationDecompositionGroup A K L Q).carrier) :
    Q = Q.comap (normalizationGaloisRingHom A K L σ.val) := by
  have hfix := commAlgIdealDecomposition_comap A (normalizationCommAlgCat A L) Q
    ((originalFiniteNormalizationDecompositionMorphism A K L Q).hom'.toFun σ)
  exact hfix.trans
    (congrArg (fun g : (commAlgAutomorphismGroup A (normalizationCommAlgCat A L)).carrier =>
      Q.comap (commAlgAutomorphismRingHom A (normalizationCommAlgCat A L) g))
      (originalFiniteNormalizationDecompositionMorphism_value A K L Q σ))

/-- The literal coefficient square contracts original decomposition
stability to the actual finite normalization prime. -/
theorem originalDecomposition_finiteNormalization_stable
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L)
    (σ : (normalizationDecompositionGroup A K L Q).carrier) :
    (finiteAbsoluteNormalizationPrime A K L Q E).map
        (actualFiniteNormalizationRestrictionRingHom A K L E σ.val) =
      finiteAbsoluteNormalizationPrime A K L Q E := by
  exact ideal_map_comap_eq_of_equivariant
    (finiteAbsoluteNormalizationAlgebra A K L E).carrier
    (normalizationCommAlgCat A L).carrier
    (finiteAbsoluteNormalizationRingMap A K L E)
    ((actualFiniteNormalizationRestriction A K L E).hom'.toFun σ.val).toRingEquiv
    ((normalizationGaloisGroupMap A K L).hom'.toFun σ.val).toRingEquiv Q
    (actualFiniteNormalizationRestrictionRingHom_inclusion A K L E σ.val)
    (originalNormalizationDecomposition_comap A K L Q σ)

/-- The prescribed finite coefficient map on the original decomposition group. -/
def actualFiniteDecompositionCoefficientMap
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (normalizationDecompositionGroup A K L Q)
      (commAlgAutomorphismGroup A (finiteAbsoluteNormalizationAlgebra A K L E)) where
  hom' := (actualFiniteNormalizationRestriction A K L E).hom'.comp
    (normalizationDecompositionInclusion A K L Q)

/-- Actual original decomposition restricts to the same native coefficient
stabilizer of the literal finite normalization prime. -/
def actualFiniteDecompositionRestriction
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (normalizationDecompositionGroup A K L Q)
      (commAlgIdealDecompositionGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)) :=
  commAlgDecompositionHomOfStabilizer A (finiteAbsoluteNormalizationAlgebra A K L E)
    (normalizationDecompositionGroup A K L Q) (finiteAbsoluteNormalizationPrime A K L Q E)
    (actualFiniteDecompositionCoefficientMap A K L Q E)
    (originalDecomposition_finiteNormalization_stable A K L Q E)

end EtaleFundamentalGroups.Inertia

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgInertiaRestriction
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Restriction to finite normalization inertia

Constructs the inclusion of original inertia into the ambient Galois group and its restriction
to the intrinsic inertia group of a finite normalization.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The actual original inertia includes into the original ambient group. -/
def actualNormalizationInertiaInclusion (Q : Ideal (integralClosure A L)) :
    GrpCat.Hom (actualNormalizationInertiaGroup A K L Q) (galoisGroupObject K L) where
  hom' := (Q.inertia Gal(L/K)).subtype

/-- The prescribed finite coefficient automorphism map on actual original inertia. -/
def actualFiniteInertiaCoefficientMap (Q : Ideal (integralClosure A L))
    (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (actualNormalizationInertiaGroup A K L Q)
      (commAlgAutomorphismGroup A (finiteAbsoluteNormalizationAlgebra A K L E)) where
  hom' := (actualFiniteNormalizationRestriction A K L E).hom'.comp
    (actualNormalizationInertiaInclusion A K L Q).hom'

/-- Actual original inertia restricts to the SAME native intrinsic finite
normalization inertia used by the canonical finite tame character. -/
def actualFiniteInertiaRestriction (Q : Ideal (integralClosure A L))
    (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (actualNormalizationInertiaGroup A K L Q)
      (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)) :=
  commAlgInertiaHomOfDifference A (finiteAbsoluteNormalizationAlgebra A K L E)
    (actualNormalizationInertiaGroup A K L Q)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (actualFiniteInertiaCoefficientMap A K L Q E)
    (originalInertia_finiteNormalization_difference A K L Q E)

end EtaleFundamentalGroups.Inertia

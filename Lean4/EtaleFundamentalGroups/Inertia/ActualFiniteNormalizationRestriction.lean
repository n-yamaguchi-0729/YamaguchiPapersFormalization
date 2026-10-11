/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteLevelFieldAlgebra
import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionGroupMap
import SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import SchemeTheory.Normalization.ScalarRestrictionGroupMap
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Galois restriction on finite normalizations

Constructs the finite Galois action on its normalization and the homomorphism restricting
ambient Galois automorphisms to those coefficient automorphisms.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The actual finite Galois action on its literal native normalization. -/
def finiteNormalizationGaloisGroupMap (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (finiteGaloisGroupObject K L E)
      (commAlgAutomorphismGroup A (finiteAbsoluteNormalizationAlgebra A K L E)) where
  hom' := (normalizationAutomorphismGroupMap A (finiteLevelFieldAlgebra A K L E)).hom'.comp
    (scalarRestrictionGroupMap A K (finiteLevelFieldAlgebra A K L E)).hom'

/-- Actual ambient Galois restriction to the intrinsic automorphism group
of the native finite normalization. Every map is constructed canonically. -/
def actualFiniteNormalizationRestriction (E : FiniteGaloisIntermediateField K L) :
    GrpCat.Hom (galoisGroupObject K L)
      (commAlgAutomorphismGroup A (finiteAbsoluteNormalizationAlgebra A K L E)) where
  hom' := (finiteNormalizationGaloisGroupMap A K L E).hom'.comp
    (finiteGaloisRestrictionGroupMap K L E).hom'

end EtaleFundamentalGroups.Inertia

end

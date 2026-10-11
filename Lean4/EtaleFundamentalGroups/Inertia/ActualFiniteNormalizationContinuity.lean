/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionContinuity
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of actual finite normalization restriction

This ambient coefficient restriction is proved locally constant before the
original inertia and the intrinsic finite inertia subgroups enter the scope.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- The existing restriction to finite normalization coefficients factors
through the locally constant finite Galois restriction. -/
theorem actualFiniteNormalizationRestriction_isLocallyConstant
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    IsLocallyConstant (actualFiniteNormalizationRestriction A K L E).hom'.toFun :=
  (finiteGaloisRestrictionGroupMap_isLocallyConstant K L E).comp
    (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun

end EtaleFundamentalGroups.Inertia

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteGaloisRestrictionGroupMap
import EtaleFundamentalGroups.Inertia.NativeGaloisGroupTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of the actual finite Galois restriction

The domain keeps its original Krull topology. Finite dimensionality makes
the target's Krull topology discrete, so the existing continuous restriction
is locally constant before any normalization or coefficient action is opened.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The actual finite Galois restriction is locally constant for the original
Krull topology, using the target's finite-dimensional discrete topology. -/
theorem finiteGaloisRestrictionGroupMap_isLocallyConstant
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (E : FiniteGaloisIntermediateField K L) :
    IsLocallyConstant (finiteGaloisRestrictionGroupMap K L E).hom'.toFun :=
  (IsLocallyConstant.iff_continuous
    (finiteGaloisRestrictionGroupMap K L E).hom'.toFun).mpr
      (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)

end EtaleFundamentalGroups.Inertia

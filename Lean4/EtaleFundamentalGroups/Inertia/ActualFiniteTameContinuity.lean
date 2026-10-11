/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaContinuity
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameMorphism
import EtaleFundamentalGroups.Inertia.ActualFiniteRootsGroupMap
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.NormalizationRootsGroup
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuity of the existing canonical tame coordinates

The SAME constructed canonical coordinate is the composite of the locally
constant actual finite inertia restriction with its finite character and
residue-root inclusion. Its source keeps the original Krull subgroup topology.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- The existing canonical finite tame coordinate is locally constant for
the original Krull subgroup topology. -/
theorem actualFiniteTameCoordinate_isLocallyConstant
    (E : FiniteGaloisIntermediateField K L) :
    IsLocallyConstant (actualFiniteTameCoordinate A K L Q E).hom'.toFun :=
  ((actualFiniteInertiaRestriction_isLocallyConstant A K L Q E).comp
    (actualFiniteCanonicalTameMorphism A K L Q E).hom'.toFun).comp
      (actualFiniteRootsGroupMap A K L Q E).hom'.toFun

/-- The SAME actual coordinate is continuous into its discrete ambient
root group, and into any other topology on that identical target carrier. -/
theorem actualFiniteTameCoordinate_continuous
    (E : FiniteGaloisIntermediateField K L)
    [TopologicalSpace (normalizationRootsGroup A L Q
      (actualFiniteStageTameOrder A K L Q E)).carrier] :
    Continuous (actualFiniteTameCoordinate A K L Q E).hom'.toFun :=
  (actualFiniteTameCoordinate_isLocallyConstant A K L Q E).continuous

end EtaleFundamentalGroups.Inertia

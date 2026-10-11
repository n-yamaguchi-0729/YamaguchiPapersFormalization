/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import SchemeTheory.RingTheory.Ramification.IdealInertiaClosed
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import SchemeTheory.Normalization.ScalarRestrictionGroupMap
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness of original normalization inertia

The topology is the original Krull topology restricted to the literal
normalization inertia subgroup. Closedness comes from the already proved
openness of the original coefficient stabilizers.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- Actual normalization inertia is closed for the original Krull topology. -/
theorem actualNormalizationInertia_isClosed (Q : Ideal (integralClosure A L)) :
    IsClosed (Q.inertia Gal(L/K)).carrier :=
  idealInertia_isClosed_of_openFixedSets
    (CommRingCat.of (normalizationCommAlgCat A L).carrier) (galoisGroupObject K L)
    (normalizationInertiaImageAction A K L) Q
    (integralClosure_fixedSet_isOpen_krull A K L)

/-- The actual original inertia group is compact in its inherited topology. -/
theorem actualNormalizationInertia_compactSpace
    (Q : Ideal (normalizationCommAlgCat A L).carrier) :
    CompactSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
  isCompact_iff_compactSpace.mp (actualNormalizationInertia_isClosed A K L Q).isCompact

end EtaleFundamentalGroups.Inertia

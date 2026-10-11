/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.EtaleFundamentalGroups.Inertia.NativeGaloisGroupTopology
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Original subgroup topology on native normalization inertia

The native actual inertia group inherits exactly the subspace topology of
its literal subgroup in the original Krull Galois group. Its topological
group and separation properties are inherited from that same subgroup.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L).carrier)

/-- The topology induced by the literal inclusion into the original Krull
Galois group, identical to the existing raw subgroup topology. -/
instance actualNormalizationInertiaGroup_topologicalSpace :
    TopologicalSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
  TopologicalSpace.induced (actualNormalizationInertiaElement A K L Q) (krullTopology K L)

instance actualNormalizationInertiaGroup_isTopologicalGroup :
    IsTopologicalGroup (actualNormalizationInertiaGroup A K L Q).carrier := by
  let : MulSemiringAction Gal(L/K) (SchemeTheory.normalizationCommAlgCat A L).carrier :=
    normalizationInertiaImageAction A K L
  exact inferInstanceAs (IsTopologicalGroup (Q.inertia Gal(L/K)))

instance actualNormalizationInertiaGroup_t2Space :
    T2Space (actualNormalizationInertiaGroup A K L Q).carrier := by
  let : MulSemiringAction Gal(L/K) (SchemeTheory.normalizationCommAlgCat A L).carrier :=
    normalizationInertiaImageAction A K L
  exact inferInstanceAs (T2Space (Q.inertia Gal(L/K)))

instance actualNormalizationInertiaGroup_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (actualNormalizationInertiaGroup A K L Q).carrier := by
  let : MulSemiringAction Gal(L/K) (SchemeTheory.normalizationCommAlgCat A L).carrier :=
    normalizationInertiaImageAction A K L
  exact inferInstanceAs (TotallyDisconnectedSpace (Q.inertia Gal(L/K)))

end EtaleFundamentalGroups.Inertia

end

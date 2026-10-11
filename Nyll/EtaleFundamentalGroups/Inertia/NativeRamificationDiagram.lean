/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeRamificationResidues
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Topology.Constructions

/-!
# The native data of the two ramification sequences

This stores group objects, their actual maps, the independent wild subgroup,
and existing topologies. It stores no exactness, normality, surjectivity,
comparison or other conclusion. The roots target is computed from the
residue data, so it cannot be replaced by an unrelated abstract group.
-/

namespace EtaleFundamentalGroups.Inertia

universe u w

/-- Data of the original ramification diagram, with its intrinsic roots target. -/
structure NativeRamificationDiagram (R : NativeRamificationResidues.{u, w}) where
  /-- Original decomposition. -/
  decomposition : GrpCat.{w}
  /-- Original inertia. -/
  inertia : GrpCat.{w}
  /-- The automorphisms of the residue extension. -/
  residueAutomorphisms : GrpCat.{w}
  /-- The actual quotient of inertia by its independent wild subgroup. -/
  tameQuotient : GrpCat.{w}
  /-- Independently defined wild inertia inside original inertia. -/
  wild : Subgroup inertia.carrier
  /-- The literal inclusion of inertia into decomposition. -/
  inertiaInclusion : GrpCat.Hom inertia decomposition
  /-- The actual residue action. -/
  residueMorphism : GrpCat.Hom decomposition residueAutomorphisms
  /-- The literal quotient projection. -/
  quotientProjection : GrpCat.Hom inertia tameQuotient
  /-- The canonical character into the computed root limit. -/
  character : GrpCat.Hom inertia R.rootsGroup
  /-- Original decomposition conjugation on inertia. -/
  conjugate : decomposition.carrier → inertia.carrier → inertia.carrier
  /-- Original residue action on the same root limit. -/
  rootsAction : decomposition.carrier → R.rootsGroup.carrier → R.rootsGroup.carrier
  /-- The original inertia topology. -/
  inertiaTopology : TopologicalSpace inertia.carrier
  /-- The literal quotient topology. -/
  tameQuotientTopology : TopologicalSpace tameQuotient.carrier

end EtaleFundamentalGroups.Inertia

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeAbsoluteRamificationResidues
import Nyll.EtaleFundamentalGroups.Inertia.NativeRamificationDiagram
import Nyll.EtaleFundamentalGroups.Inertia.NativeRamificationResidues
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Topology.Constructions

/-!
# The native absolute ramification diagram

The group data are shared with the existing original DVR diagram. This
retains its independent P, literal I/P and existing subgroup/quotient
topologies once. The absolute diagram adds exactly the residue map and
full-target character. Its roots action is computed from that SAME residue
map and the existing coefficient action, rather than stored arbitrarily.
No exactness, closure, normality, continuity or comparison fact is input data.
-/

namespace EtaleFundamentalGroups.Inertia

universe u w

/-- The unchanged original D, I, P and I/P data, independent of the roots target. -/
structure NativeAbsoluteRamificationGroups where
  /-- The original decomposition group. -/
  decomposition : GrpCat.{w}
  /-- The original inertia group. -/
  inertia : GrpCat.{w}
  /-- The literal quotient of inertia by its independent wild subgroup. -/
  tameQuotient : GrpCat.{w}
  /-- The independently defined wild subgroup. -/
  wild : Subgroup inertia.carrier
  /-- Original inclusion of inertia into decomposition. -/
  inertiaInclusion : GrpCat.Hom inertia decomposition
  /-- The literal quotient projection. -/
  quotientProjection : GrpCat.Hom inertia tameQuotient
  /-- Original decomposition conjugation on inertia. -/
  conjugate : decomposition.carrier → inertia.carrier → inertia.carrier
  /-- The existing inertia topology. -/
  inertiaTopology : TopologicalSpace inertia.carrier
  /-- The existing quotient topology. -/
  tameQuotientTopology : TopologicalSpace tameQuotient.carrier

/-- Share actual group objects and topologies from the existing DVR diagram. -/
def nativeAbsoluteRamificationGroupsOfDiagram
    (R : NativeRamificationResidues.{u, w}) (D : NativeRamificationDiagram R) :
    NativeAbsoluteRamificationGroups.{w} where
  decomposition := D.decomposition
  inertia := D.inertia
  tameQuotient := D.tameQuotient
  wild := D.wild
  inertiaInclusion := D.inertiaInclusion
  quotientProjection := D.quotientProjection
  conjugate := D.conjugate
  inertiaTopology := D.inertiaTopology
  tameQuotientTopology := D.tameQuotientTopology

/-- The two actual absolute maps into intrinsically computed full targets. -/
structure NativeAbsoluteRamificationDiagram
    (R : NativeAbsoluteRamificationResidues.{u, w}) (G : NativeAbsoluteRamificationGroups.{w}) where
  /-- The SAME canonical absolute residue action. -/
  residueMorphism : GrpCat.Hom G.decomposition R.residueAutomorphisms
  /-- The SAME canonical character, postcomposed into the literal full roots group. -/
  character : GrpCat.Hom G.inertia R.rootsGroup

namespace NativeAbsoluteRamificationDiagram

variable {R : NativeAbsoluteRamificationResidues.{u, w}}
  {G : NativeAbsoluteRamificationGroups.{w}} (D : NativeAbsoluteRamificationDiagram R G)

/-- Decomposition acts by the SAME stored residue map on the full root coefficients. -/
def rootsAction (d : G.decomposition.carrier) (x : R.rootsGroup.carrier) :
    R.rootsGroup.carrier :=
  R.rootsAction (D.residueMorphism.hom'.toFun d) x

end NativeAbsoluteRamificationDiagram

end EtaleFundamentalGroups.Inertia

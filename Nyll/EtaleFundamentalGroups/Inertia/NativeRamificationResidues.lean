/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Nyll.EtaleFundamentalGroups.Inertia.RestrictedPrimeToRootsGroupSystem
import Nyll.ProCGroups.InverseSystems.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Native residue data for the ramification diagram

Only the two coefficient fields and the actual set of invertible natural
exponents are stored. The target is computed as the literal root inverse
limit over these degrees. No root group or comparison is supplied separately.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u w

/-- The coefficient fields and degrees underlying a literal tame-root limit. -/
structure NativeRamificationResidues where
  /-- The original base residue field. -/
  baseResidue : Type u
  /-- Its retained field structure. -/
  [baseResidueField : Field baseResidue]
  /-- The residue field containing the roots. -/
  residue : Type w
  /-- Its retained field structure. -/
  [residueField : Field residue]
  /-- The actual residue-invertible natural degrees. -/
  degrees : Set (InvertibleExponent baseResidue)

attribute [local instance] NativeRamificationResidues.baseResidueField
  NativeRamificationResidues.residueField

namespace NativeRamificationResidues

/-- The literal power-transition roots system on the stored degrees. -/
def rootsSystem (R : NativeRamificationResidues.{u, w}) :
    InverseSystem.{0, w} (I := {n : InvertibleExponent R.baseResidue // R.degrees n}) :=
  (primeToRootsSystem R.baseResidue R.residue).restrict R.degrees

/-- The same canonical coordinatewise root groups. -/
instance rootsSystem_groups (R : NativeRamificationResidues.{u, w}) :
    ∀ n : {n : InvertibleExponent R.baseResidue // R.degrees n}, Group ((rootsSystem R).X n) :=
  fun n => primeToRootsSystem_group R.baseResidue R.residue n.val

instance rootsSystem_isGroupSystem (R : NativeRamificationResidues.{u, w}) :
    IsGroupSystem (rootsSystem R) :=
  primeToRootsSystem_restrict_isGroupSystem R.baseResidue R.residue R.degrees

/-- The actual inverse limit, retaining its coordinatewise group operations. -/
def rootsGroup (R : NativeRamificationResidues.{u, w}) : GrpCat.{w} :=
  GrpCat.of (rootsSystem R).inverseLimit

/-- The root limit retains the original inverse-limit topology. -/
instance rootsGroup_topologicalSpace (R : NativeRamificationResidues.{u, w}) :
    TopologicalSpace (rootsGroup R).carrier :=
  inferInstanceAs (TopologicalSpace (rootsSystem R).inverseLimit)

end NativeRamificationResidues

end EtaleFundamentalGroups.Inertia

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import ProCGroups.InverseSystems.GroupSystemRestriction

/-!
# The canonical group-system class on a restricted roots system

The full exponent group family is closed here, with only the two coefficient
fields present. The result retains exactly the restricted prime-to-roots
group family, so original DVR consumers need not reopen the full index.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v

/-- The literal restricted root system is a group system for the SAME
prime-to-roots groups, with the full exponent family closed in this owner. -/
theorem primeToRootsSystem_restrict_isGroupSystem
    (k : Type u) (R : Type v) [Field k] [Field R]
    (J : Set (InvertibleExponent k)) :
    let : ∀ j : J, Group (((primeToRootsSystem k R).restrict J).X j) :=
      fun j => primeToRootsSystem_group k R j.val
    IsGroupSystem ((primeToRootsSystem k R).restrict J) := by
  intro rootGroups
  let fullGroups : ∀ n : InvertibleExponent k, Group ((primeToRootsSystem k R).X n) :=
    fun n => primeToRootsSystem_group k R n
  have fullGroupSystem : IsGroupSystem (primeToRootsSystem k R) :=
    primeToRootsSystem_isGroupSystem k R
  exact InverseSystem.restrict_isGroupSystem (primeToRootsSystem k R) J

end EtaleFundamentalGroups.Inertia

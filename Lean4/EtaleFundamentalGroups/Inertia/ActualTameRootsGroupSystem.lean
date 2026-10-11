/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteTameRootsSystem
import EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import EtaleFundamentalGroups.Inertia.RestrictedPrimeToRootsGroupSystem

/-!
# The existing actual roots system as a group system

Supplies the exact stage-group family and group-system class on the existing
actual roots system. Both are the original prime-to-roots groups and their
literal restriction; no group operation or inverse system is replaced.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups.InverseSystems

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The SAME existing prime-to-roots stage-group family at the actual degrees. -/
noncomputable instance actualFiniteTameRootsSystem_groups :
    ∀ n : Subtype (actualFiniteTameDegreeSet A K L Q),
      Group ((actualFiniteTameRootsSystem A K L Q).X n) :=
  fun n => primeToRootsSystem_group (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A L).carrier ⧸ Q) n.val

/-- The SAME existing restricted transition maps are group homomorphisms
for that exact prime-to-roots stage-group family. -/
instance actualFiniteTameRootsSystem_isGroupSystem :
    IsGroupSystem (actualFiniteTameRootsSystem A K L Q) :=
  primeToRootsSystem_restrict_isGroupSystem (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A L).carrier ⧸ Q) (actualFiniteTameDegreeSet A K L Q)

end EtaleFundamentalGroups.Inertia

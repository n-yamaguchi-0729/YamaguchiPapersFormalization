/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualFiniteWildImage
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaTowerRestriction
import EtaleFundamentalGroups.Inertia.SubgroupRestrictionOfImage
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Surjective actual finite wild restrictions

The induced map uses the literal actual inertia restriction. Its image
equality was proved from the original data, so preservation and surjectivity
are conclusions, with no comparison premise supplied by a caller.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
  (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F)

/-- The actual induced restriction on the SAME intrinsic finite wild groups. -/
def actualFiniteWildTowerRestriction :
    GrpCat.Hom (actualFiniteWildGroup A K L Q F) (actualFiniteWildGroup A K L Q E) where
  hom' := subgroupRestrictionOfImage
    (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'
    (actualFiniteWildSubgroup A K L Q F) (actualFiniteWildSubgroup A K L Q E)
    (actualFiniteWildSubgroup_map A K L Q E F hEF)

/-- On its underlying inertia element this is precisely the actual rho. -/
theorem actualFiniteWildTowerRestriction_val
    (sigma : (actualFiniteWildGroup A K L Q F).carrier) :
    ((actualFiniteWildTowerRestriction A K L Q E F hEF).hom'.toFun sigma).val =
      (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'.toFun sigma.val :=
  subgroupRestrictionOfImage_val
    (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'
    (actualFiniteWildSubgroup A K L Q F) (actualFiniteWildSubgroup A K L Q E)
    (actualFiniteWildSubgroup_map A K L Q E F hEF) sigma

/-- The same induced actual wild restriction is surjective. -/
theorem actualFiniteWildTowerRestriction_surjective :
    Function.Surjective (actualFiniteWildTowerRestriction A K L Q E F hEF).hom'.toFun :=
  subgroupRestrictionOfImage_surjective
    (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'
    (actualFiniteWildSubgroup A K L Q F) (actualFiniteWildSubgroup A K L Q E)
    (actualFiniteWildSubgroup_map A K L Q E F hEF)

end EtaleFundamentalGroups.Inertia

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsCoefficientMap
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction

/-!
# The original decomposition action on the SAME actual tame roots group

The action is the original quotient-residue action on every existing root
coordinate. Its plain application and scalar law close the action's native
permutation data before the original character is compared with it.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The canonical original decomposition action on the SAME actual roots group. -/
def actualTameRootsAction :
    (normalizationDecompositionGroup A K L Q).carrier →*
      Equiv.Perm (actualTameRootsGroup A K L Q).carrier :=
  (restrictedRootsCoefficientAction (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A L).carrier ⧸ Q)
    (actualFiniteTameDegreeSet A K L Q)).comp
      (actualNormalizationQuotientAction A K L Q)

/-- Plain application of the SAME constructed decomposition action. -/
def actualTameRootsAction_apply
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (x : (actualTameRootsGroup A K L Q).carrier) :
    (actualTameRootsGroup A K L Q).carrier :=
  ((actualTameRootsAction A K L Q).toFun d).toFun x

/-- Every literal scalar coordinate carries the original quotient-residue action. -/
theorem actualTameRootsAction_projection
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (x : (actualTameRootsGroup A K L Q).carrier)
    (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    actualTameRootsScalar A K L Q n (actualTameRootsAction_apply A K L Q d x) =
      ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
        (actualTameRootsScalar A K L Q n x) := rfl

/-- The original decomposition action fixes the existing identity element. -/
theorem actualTameRootsAction_one
    (d : (normalizationDecompositionGroup A K L Q).carrier) :
    actualTameRootsAction_apply A K L Q d 1 = 1 :=
  actualTameRootsCoefficientMap_one A K L Q
    ((actualNormalizationQuotientAction A K L Q).toFun d).toRingHom

/-- The original decomposition action preserves the existing multiplication. -/
theorem actualTameRootsAction_mul
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (x y : (actualTameRootsGroup A K L Q).carrier) :
    actualTameRootsAction_apply A K L Q d (x * y) =
      actualTameRootsAction_apply A K L Q d x * actualTameRootsAction_apply A K L Q d y :=
  actualTameRootsCoefficientMap_mul A K L Q
    ((actualNormalizationQuotientAction A K L Q).toFun d).toRingHom x y

end EtaleFundamentalGroups.Inertia

end

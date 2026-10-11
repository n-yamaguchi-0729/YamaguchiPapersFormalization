/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameRootsGroup
import EtaleFundamentalGroups.Inertia.RestrictedRootsCoefficientAction

/-!
# Coefficient maps on the SAME native tame roots group

The coefficient map acts on the existing root coordinates. Its group laws
are proved here before an original decomposition element is introduced.
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

/-- Apply a coefficient homomorphism to the coordinates of the SAME actual limit. -/
def actualTameRootsCoefficientMap
    (f : (normalizationCommAlgCat A L).carrier ⧸ Q →+*
      (normalizationCommAlgCat A L).carrier ⧸ Q) :
    (actualTameRootsGroup A K L Q).carrier → (actualTameRootsGroup A K L Q).carrier :=
  restrictedRootsCoefficientMap (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A L).carrier ⧸ Q) (actualFiniteTameDegreeSet A K L Q) f

/-- The actual coefficient map preserves the existing identity element. -/
theorem actualTameRootsCoefficientMap_one
    (f : (normalizationCommAlgCat A L).carrier ⧸ Q →+*
      (normalizationCommAlgCat A L).carrier ⧸ Q) :
    actualTameRootsCoefficientMap A K L Q f 1 = 1 :=
  restrictedRootsCoefficientMap_one (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A L).carrier ⧸ Q) (actualFiniteTameDegreeSet A K L Q) f

/-- The actual coefficient map preserves the existing multiplication. -/
theorem actualTameRootsCoefficientMap_mul
    (f : (normalizationCommAlgCat A L).carrier ⧸ Q →+*
      (normalizationCommAlgCat A L).carrier ⧸ Q)
    (x y : (actualTameRootsGroup A K L Q).carrier) :
    actualTameRootsCoefficientMap A K L Q f (x * y) =
      actualTameRootsCoefficientMap A K L Q f x * actualTameRootsCoefficientMap A K L Q f y :=
  restrictedRootsCoefficientMap_mul (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A L).carrier ⧸ Q) (actualFiniteTameDegreeSet A K L Q) f x y

end EtaleFundamentalGroups.Inertia

end

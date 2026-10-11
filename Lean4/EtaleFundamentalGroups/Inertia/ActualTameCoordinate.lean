/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteTameRootsSystem
import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameValueTower
import EtaleFundamentalGroups.Inertia.RootsOfUnityDegreeEquiv

/-!
# Canonical tame coordinates indexed by the actual degrees

At an actual degree, choose a finite stage realizing that degree and apply
the existing canonical e/n character. Its value is transported through the
existing maximal-quotient residue equivalence. The evaluation theorem proves
independence from the realizing stage.
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

/-- The actual quotient-valued coordinate at an actual tame degree. -/
def actualTameCoordinate (n : Subtype (actualFiniteTameDegreeSet A K L Q)) :
    (actualNormalizationInertiaGroup A K L Q).carrier →*
      rootsOfUnity n.val.val ((normalizationCommAlgCat A L).carrier ⧸ Q) :=
  (rootsOfUnityDegreeEquiv ((normalizationCommAlgCat A L).carrier ⧸ Q)
    (congrArg Subtype.val n.property.choose_spec)).toMonoidHom.comp
      (actualFiniteQuotientTameCoordinate A K L Q n.property.choose)

/-- Every realizing finite stage gives the same scalar value. This proves
choice independence using the actual common-upper-stage comparison. -/
theorem actualTameCoordinate_eval
    (n : Subtype (actualFiniteTameDegreeSet A K L Q))
    (E : FiniteGaloisIntermediateField K L)
    (hE : actualFiniteStageTameIndex A K L Q E = n.val)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (((actualTameCoordinate A K L Q n).toFun σ).val).val =
      actualFiniteQuotientTameValue A K L Q E σ := by
  change actualFiniteQuotientTameValue A K L Q n.property.choose σ = _
  exact actualFiniteQuotientTameValue_eq_of_tameOrder_eq A K L Q n.property.choose E
    (congrArg Subtype.val (n.property.choose_spec.trans hE.symm)) σ

end EtaleFundamentalGroups.Inertia

end

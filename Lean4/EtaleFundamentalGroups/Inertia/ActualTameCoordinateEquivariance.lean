/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameEquivariance
import EtaleFundamentalGroups.Inertia.ActualTameCoordinate

/-!
# Equivariance at every actual tame degree

The already proved stage-independent evaluation theorem transfers finite
quotient scalar equivariance to the SAME coordinate of the original theta.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualTameCoordinate_conjugate_scalar
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (n : Subtype (actualFiniteTameDegreeSet A K L Q))
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    ((actualTameCoordinate A K L Q n).toFun
        (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).val.val =
      ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
        ((actualTameCoordinate A K L Q n).toFun σ).val.val :=
  (actualTameCoordinate_eval A K L Q n n.property.choose n.property.choose_spec
    (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).trans
    ((actualFiniteQuotientTameValue_conjugate A K L Q n.property.choose d σ).trans
      (congrArg ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
        (actualTameCoordinate_eval A K L Q n n.property.choose n.property.choose_spec σ).symm))

end EtaleFundamentalGroups.Inertia

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteTameNormalizationMap
import EtaleFundamentalGroups.Inertia.ActualFiniteRawTameValue

/-!
# Scalar values of the actual finite quotient coordinate

The scalar is the projection of the SAME constructed quotient coordinate.
Its canonical normalized-raw evaluation closes the root group at one stage;
subsequent tower comparisons can work entirely with scalars.
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

/-- The scalar projection of the actual finite quotient coordinate. -/
def actualFiniteQuotientTameValue (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (normalizationCommAlgCat A L).carrier ⧸ Q :=
  ((actualFiniteQuotientTameCoordinate A K L Q E).toFun σ).val.val

/-- The quotient scalar is the canonical quotient comparison of the
original finite root scalar. The comparison involves only one finite stage. -/
theorem actualFiniteQuotientTameValue_eq_residue
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteQuotientTameValue A K L Q E σ =
      (normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun
        ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val.val := rfl

/-- The actual quotient scalar agrees with the independently constructed
raw value and its actual e/n normalization. -/
theorem actualFiniteQuotientTameValue_eq_normalizationMap
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteQuotientTameValue A K L Q E σ =
      (normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun
        ((actualFiniteTameNormalizationMap A K L Q E).toFun
          (actualFiniteRawTameValue A K L Q E σ)) := by
  exact (actualFiniteQuotientTameValue_eq_residue A K L Q E σ).trans
    (congrArg (normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun
      (actualFiniteTameCoordinate_eq_normalizationMap A K L Q E σ))

end EtaleFundamentalGroups.Inertia

end

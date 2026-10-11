/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameScalarRestrictionData
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate

/-!
# Actual finite tame coordinate equivariance

Combines the proved canonical character conjugation and the independently
proved literal residue-embedding action square at this SAME finite stage.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualFiniteTameCoordinate_conjugate_scalar
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    ((actualFiniteTameCoordinate A K L Q E).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).val.val =
      (actualNormalizationResidueFieldMap A K L Q d).toFun
        ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val.val := by
  exact (actualTameScalarRestrictionData_character A K L Q E
      (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).trans
    ((congrArg (actualTameScalarRestrictionData A K L Q E).residueMap
      ((congrArg (actualFiniteTameScalarData A K L Q E).character
        (actualTameScalarRestrictionData_conjugate A K L Q E d σ)).trans
        (actualFiniteTameScalarData_equivariant A K L Q E
          ((actualTameScalarRestrictionData A K L Q E).decompositionMap d)
          ((actualTameScalarRestrictionData A K L Q E).inertiaMap σ)))).trans
      ((actualTameScalarRestrictionData_residue A K L Q E d
        ((actualFiniteTameScalarData A K L Q E).character
          ((actualTameScalarRestrictionData A K L Q E).inertiaMap σ))).trans
        (congrArg ((actualTameCoordinateScalarData A K L Q E).action d)
          (actualTameScalarRestrictionData_character A K L Q E σ).symm)))

end EtaleFundamentalGroups.Inertia

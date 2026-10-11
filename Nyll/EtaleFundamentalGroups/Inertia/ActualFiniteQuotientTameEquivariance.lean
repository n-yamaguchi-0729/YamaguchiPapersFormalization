/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinateEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationQuotientActionComparison
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteQuotientTameValue

/-!
# Equivariance of the actual quotient scalar coordinates

The existing canonical maximal-quotient equivalence transports the proved
finite scalar action to the SAME quotient coordinate used by global theta.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualFiniteQuotientTameValue_conjugate
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteQuotientTameValue A K L Q E
        (originalFiniteNormalizationInertiaConjugate A K L Q d σ) =
      ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
        (actualFiniteQuotientTameValue A K L Q E σ) :=
  (actualFiniteQuotientTameValue_eq_residue A K L Q E
    (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).trans
    ((congrArg (normalizationMaximalQuotientResidueEquiv A L Q).symm.toFun
      (actualFiniteTameCoordinate_conjugate_scalar A K L Q E d σ)).trans
      ((actualNormalizationResidueFieldMap_toQuotient A K L Q d
        ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val.val).trans
        (congrArg ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
          (actualFiniteQuotientTameValue_eq_residue A K L Q E σ).symm)))

end EtaleFundamentalGroups.Inertia

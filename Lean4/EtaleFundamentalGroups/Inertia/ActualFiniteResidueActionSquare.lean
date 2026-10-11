/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteResidueAction
import EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
import EtaleFundamentalGroups.Inertia.ResidueMapCoefficientNaturality
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationInclusionSquare

/-!
# The actual finite residue-action square

The canonical residue embedding intertwines the actual finite stabilizer
action and the original decomposition residue action. Every coefficient
formula and the underlying inclusion square are independently proved.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualFiniteNormalizationResidueMap_action
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (d : (normalizationDecompositionGroup A K L Q).carrier) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∀ x : (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField,
      (actualFiniteNormalizationResidueMap A K L Q E).toFun
          ((actualFiniteDecompositionResidueFieldMap A K L Q E d).toFun x) =
        (actualNormalizationResidueFieldMap A K L Q d).toFun
          ((actualFiniteNormalizationResidueMap A K L Q E).toFun x) := by
  intro finitePrime x
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsMaximal :=
    actualFiniteNormalizationPrime_isMaximal A K L Q E
  exact residueMap_coefficient_naturality
    (finiteAbsoluteNormalizationPrime A K L Q E) Q
    (finiteAbsoluteNormalizationRingMap A K L E) rfl
    (actualFiniteNormalizationRestrictionRingHom A K L E d.val)
    (normalizationGaloisRingHom A K L d.val)
    (actualFiniteDecompositionResidueFieldMap A K L Q E d)
    (actualNormalizationResidueFieldMap A K L Q d)
    (actualFiniteDecompositionResidueFieldMap_coefficient A K L Q E d)
    (actualNormalizationResidueFieldMap_coefficient A K L Q d)
    (actualFiniteNormalizationRestrictionRingHom_inclusion A K L E d.val) x

end EtaleFundamentalGroups.Inertia

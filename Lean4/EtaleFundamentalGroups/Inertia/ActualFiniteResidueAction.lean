/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgStabilizerResidueCoefficients
import EtaleFundamentalGroups.Inertia.ActualFiniteDecompositionRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage

/-!
# The actual finite restricted decomposition residue action

This is the existing intrinsic stabilizer residue morphism evaluated on
the actual finite restriction, with its literal coefficient formula.
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

/-- The literal finite prime is maximal because it is a nonzero Dedekind prime. -/
theorem actualFiniteNormalizationPrime_isMaximal (E : FiniteGaloisIntermediateField K L) :
    (finiteAbsoluteNormalizationPrime A K L Q E).IsMaximal := by
  have : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  exact (finiteAbsoluteNormalizationPrime_isPrime A K L Q E).isMaximal
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The actual finite stabilizer acts on its residue field through the SAME native morphism. -/
def actualFiniteDecompositionResidueFieldMap (E : FiniteGaloisIntermediateField K L)
    (d : (normalizationDecompositionGroup A K L Q).carrier) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField →+*
      (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField := by
  intro finitePrime
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsMaximal :=
    actualFiniteNormalizationPrime_isMaximal A K L Q E
  exact commAlgDecompositionResidueRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    ((actualFiniteDecompositionRestriction A K L Q E).hom'.toFun d)

theorem actualFiniteDecompositionResidueFieldMap_coefficient
    (E : FiniteGaloisIntermediateField K L)
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (b : (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (actualFiniteDecompositionResidueFieldMap A K L Q E d).toFun
        ((algebraMap (finiteAbsoluteNormalizationAlgebra A K L E).carrier
          (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField).toFun b) =
      (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E).carrier
        (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField).toFun
        ((actualFiniteNormalizationRestrictionRingHom A K L E d.val).toFun b) := by
  intro finitePrime
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsMaximal :=
    actualFiniteNormalizationPrime_isMaximal A K L Q E
  exact commAlgStabilizerResidueRingHom_coefficient A
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    ((actualFiniteDecompositionRestriction A K L Q E).hom'.toFun d) b

end EtaleFundamentalGroups.Inertia

end

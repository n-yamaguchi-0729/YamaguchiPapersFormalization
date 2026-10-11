/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueSequence
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction

/-!
# The actual absolute residue coefficient square

The original decomposition morphism to the separable residue Galois group
acts through the same literal quotient ring action used by the tame character.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Applying the original absolute residue morphism and then the coefficient
inclusion is the same as applying the original literal quotient action. -/
theorem normalizationAbsoluteResidueMorphism_commutes
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (z : (nativeSeparableResidueField (IsLocalRing.ResidueField A)
      (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)).α) :
    nativeSeparableResidueActionScalar (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
        ((normalizationAbsoluteResidueMorphism A K Ω Q).hom'.toFun d) z =
      actualNormalizationQuotientActionScalar A K Ω Q d
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) z) := by
  exact (normalizationAbsoluteResidueIso_commutes A K Ω Q
    ((normalizationResidueMorphism A K Ω Q).hom'.toFun d) z).trans
      (actualNormalizationQuotientActionScalar_eq_residueAction A K Ω Q d
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) z)).symm

end EtaleFundamentalGroups.Inertia

end

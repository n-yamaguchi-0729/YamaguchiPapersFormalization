/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationSeparableRoots
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueAction
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsAction

/-!
# The original decomposition action on the full separable roots target

This is the coefficient action of the SAME original absolute residue
morphism. Its scalar square is obtained from the concrete residue square
and the coordinate formula of the full roots action.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

/-- The original decomposition action factors through the original absolute residue map. -/
def actualSeparableRootsAction :
    (normalizationDecompositionGroup A K Ω Q).carrier →*
      Equiv.Perm (normalizationSeparableRootsGroup A Ω Q).carrier :=
  (normalizationSeparableRootsAction A Ω Q).comp
    (normalizationAbsoluteResidueMorphism A K Ω Q).hom'

/-- Plain application retains the exact original residue action. -/
def actualSeparableRootsAction_apply
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    (normalizationSeparableRootsGroup A Ω Q).carrier :=
  ((actualSeparableRootsAction A K Ω Q).toFun d).toFun x

/-- Every full scalar coordinate is acted on by the SAME literal quotient automorphism. -/
theorem actualSeparableRootsAction_scalar
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (n : InvertibleExponent (IsLocalRing.ResidueField A))
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    normalizationSeparableRootsScalar A Ω Q n
      (actualSeparableRootsAction_apply A K Ω Q d x) =
      actualNormalizationQuotientActionScalar A K Ω Q d
        (normalizationSeparableRootsScalar A Ω Q n x) := by
  exact (nativeSeparableRootsAction_scalar (IsLocalRing.ResidueField A)
    (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q)
    ((normalizationAbsoluteResidueMorphism A K Ω Q).hom'.toFun d) n x).trans
      (normalizationAbsoluteResidueMorphism_commutes A K Ω Q d
        (nativeSeparableRootsCoordinate (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A Ω Q)
          (normalizationResidueFieldAlgebra A Ω Q) n x))

/-- The current actual tame action has that same closed scalar computation. -/
theorem actualTameRootsAction_scalar
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (n : Subtype (actualFiniteTameDegreeSet A K Ω Q))
    (x : (actualTameRootsGroup A K Ω Q).carrier) :
    actualTameRootsScalar A K Ω Q n (actualTameRootsAction_apply A K Ω Q d x) =
      actualNormalizationQuotientActionScalar A K Ω Q d
        (actualTameRootsScalar A K Ω Q n x) :=
  actualTameRootsAction_projection A K Ω Q d x n

end EtaleFundamentalGroups.Inertia

end

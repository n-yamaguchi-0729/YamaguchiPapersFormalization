/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteTameCofinality
import EtaleFundamentalGroups.Inertia.ActualTameRootsAction
import EtaleFundamentalGroups.Inertia.ActualSeparableRootsAction

/-!
# The actual equivariant separable tame-roots comparison

The coefficient inclusion is restricted along the proved cofinality of
the SAME actual finite tame-degree range. Its inverse is the requested
continuous group equivalence from the SAME actual roots group to the full
separable roots limit. The coordinate square identifies both original
decomposition actions, rather than defining one by transport.
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

/-- The actual cofinal comparison as a homeomorphism, before group structures are joined. -/
def actualSeparableRootsComparisonHomeomorph :
    (normalizationSeparableRootsGroup A Ω Q).carrier ≃ₜ
      (actualTameRootsGroup A K Ω Q).carrier :=
  normalizationSeparableRootsRestrictionHomeomorph A Ω Q
    (actualFiniteTameDegreeSet A K Ω Q) (actualFiniteTameDegreeSet_cofinal A K Ω Q)

/-- The same actual cofinal comparison as a multiplicative equivalence. -/
def actualSeparableRootsComparisonMulEquiv :
    (normalizationSeparableRootsGroup A Ω Q).carrier ≃*
      (actualTameRootsGroup A K Ω Q).carrier :=
  normalizationSeparableRootsRestrictionMulEquiv A Ω Q
    (actualFiniteTameDegreeSet A K Ω Q) (actualFiniteTameDegreeSet_cofinal A K Ω Q)

/-- Both constructed comparisons have the exact same forward function. -/
theorem actualSeparableRootsComparisonMulEquiv_toFun :
    (actualSeparableRootsComparisonMulEquiv A K Ω Q).toFun =
      (actualSeparableRootsComparisonHomeomorph A K Ω Q).toFun := rfl

/-- Assemble continuity and multiplication after the actual degree interface has closed. -/
def actualSeparableRootsComparison :
    (normalizationSeparableRootsGroup A Ω Q).carrier ≃ₜ*
      (actualTameRootsGroup A K Ω Q).carrier :=
  ContinuousMulEquiv.mk' (actualSeparableRootsComparisonHomeomorph A K Ω Q) (by
    intro x y
    exact (actualSeparableRootsComparisonMulEquiv A K Ω Q).map_mul x y)

/-- Plain application closes the comparison's topology and group dictionaries. -/
def actualSeparableRootsComparison_apply
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    (actualTameRootsGroup A K Ω Q).carrier :=
  normalizationSeparableRootsRestrictionMap A Ω Q
    (actualFiniteTameDegreeSet A K Ω Q) (actualFiniteTameDegreeSet_cofinal A K Ω Q) x

/-- The assembled continuous group equivalence retains the literal comparison function. -/
theorem actualSeparableRootsComparison_toFun :
    (actualSeparableRootsComparison A K Ω Q).toFun =
      actualSeparableRootsComparison_apply A K Ω Q := rfl

/-- The characteristic retained-coordinate law of the actual comparison. -/
theorem actualSeparableRootsComparison_scalar
    (n : Subtype (actualFiniteTameDegreeSet A K Ω Q))
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    actualTameRootsScalar A K Ω Q n (actualSeparableRootsComparison_apply A K Ω Q x) =
      normalizationSeparableRootsScalar A Ω Q n.val x :=
  normalizationSeparableRootsRestrictionMap_scalar A Ω Q
    (actualFiniteTameDegreeSet A K Ω Q) (actualFiniteTameDegreeSet_cofinal A K Ω Q) n x

/-- Root inclusion and cofinal restriction intertwine the SAME original D actions. -/
theorem actualSeparableRootsComparison_equivariant
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    actualSeparableRootsComparison_apply A K Ω Q (actualSeparableRootsAction_apply A K Ω Q d x) =
      actualTameRootsAction_apply A K Ω Q d (actualSeparableRootsComparison_apply A K Ω Q x) := by
  apply actualTameRootsScalar_ext A K Ω Q
  intro n
  rw [actualSeparableRootsComparison_scalar, actualSeparableRootsAction_scalar,
    actualTameRootsAction_scalar, actualSeparableRootsComparison_scalar]

/-- The SAME actual tame roots group is continuously isomorphic to the full κsep roots limit. -/
def actualTameRootsSeparableEquiv :
    (actualTameRootsGroup A K Ω Q).carrier ≃ₜ*
      (normalizationSeparableRootsGroup A Ω Q).carrier :=
  (actualSeparableRootsComparison A K Ω Q).symm

/-- The requested-direction equivalence preserves the SAME original decomposition action. -/
theorem actualTameRootsSeparableEquiv_equivariant
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (x : (actualTameRootsGroup A K Ω Q).carrier) :
    (actualTameRootsSeparableEquiv A K Ω Q).toFun (actualTameRootsAction_apply A K Ω Q d x) =
      actualSeparableRootsAction_apply A K Ω Q d
        ((actualTameRootsSeparableEquiv A K Ω Q).toFun x) := by
  apply (actualSeparableRootsComparison A K Ω Q).injective
  exact ((actualSeparableRootsComparison A K Ω Q).apply_symm_apply
    (actualTameRootsAction_apply A K Ω Q d x)).trans
      ((congrArg (actualTameRootsAction_apply A K Ω Q d)
        ((actualSeparableRootsComparison A K Ω Q).apply_symm_apply x).symm).trans
          (actualSeparableRootsComparison_equivariant A K Ω Q d
            ((actualSeparableRootsComparison A K Ω Q).symm.toFun x)).symm)

end EtaleFundamentalGroups.Inertia

end

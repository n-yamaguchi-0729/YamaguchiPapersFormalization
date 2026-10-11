/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsSeparableEquiv
import Nyll.EtaleFundamentalGroups.Inertia.ActualSeparableRootsAction
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsAction
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The actual separable roots comparison as a shared group morphism

The algebraic inverse comparison supplies the literal group map. Its
function is the SAME continuous comparison; injectivity and surjectivity
are proved before introducing topologies. The character consumes this
actual map, so its kernel calculation does not reopen root topologies.
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

/-- The SAME inverse comparison, with its group structure retained independently. -/
def actualTameRootsSeparableMap :
    GrpCat.Hom (actualTameRootsGroup A K Ω Q) (normalizationSeparableRootsGroup A Ω Q) :=
  GrpCat.ofHom (actualSeparableRootsComparisonMulEquiv A K Ω Q).symm.toMonoidHom

/-- The stored group map is exactly the proved continuous comparison's function. -/
theorem actualTameRootsSeparableMap_toFun :
    (actualTameRootsSeparableMap A K Ω Q).hom'.toFun =
      (actualTameRootsSeparableEquiv A K Ω Q).toFun := rfl

/-- Injectivity belongs to the actual algebraic inverse comparison. -/
theorem actualTameRootsSeparableMap_injective :
    Function.Injective (actualTameRootsSeparableMap A K Ω Q).hom'.toFun :=
  (actualSeparableRootsComparisonMulEquiv A K Ω Q).symm.injective

/-- Surjectivity belongs to that same algebraic inverse comparison. -/
theorem actualTameRootsSeparableMap_surjective :
    Function.Surjective (actualTameRootsSeparableMap A K Ω Q).hom'.toFun :=
  (actualSeparableRootsComparisonMulEquiv A K Ω Q).symm.surjective

/-- The existing comparison topology makes the SAME stored group map continuous. -/
theorem actualTameRootsSeparableMap_continuous :
    Continuous (actualTameRootsSeparableMap A K Ω Q).hom'.toFun :=
  (actualTameRootsSeparableEquiv A K Ω Q).continuous_toFun

/-- The stored map retains the two original decomposition actions. -/
theorem actualTameRootsSeparableMap_equivariant
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (x : (actualTameRootsGroup A K Ω Q).carrier) :
    (actualTameRootsSeparableMap A K Ω Q).hom'.toFun
        (actualTameRootsAction_apply A K Ω Q d x) =
      actualSeparableRootsAction_apply A K Ω Q d
        ((actualTameRootsSeparableMap A K Ω Q).hom'.toFun x) :=
  actualTameRootsSeparableEquiv_equivariant A K Ω Q d x

end EtaleFundamentalGroups.Inertia

end

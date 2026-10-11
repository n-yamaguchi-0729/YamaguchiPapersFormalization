/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealWildSubgroup
import EtaleFundamentalGroups.Inertia.CommAlgIdealWildProperties
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.ActualFiniteTameGroups
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.GroupTheory.Index

/-!
# The actual intrinsic finite wild subgroup and group

The original DVR, Galois extension and chosen prime supply the same native
principal-unit subgroup at every finite stage. Its cardinality and index
remain the previously constructed wild and tame orders.
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

/-- The actual intrinsic wild subgroup at a finite Galois stage. -/
def actualFiniteWildSubgroup (E : FiniteGaloisIntermediateField K L) :
    Subgroup (actualFiniteStageInertiaGroup A K L Q E).carrier := by
  have dB : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact commAlgIdealWildSubgroup A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The same subgroup as a native group object, for its induced restrictions. -/
def actualFiniteWildGroup (E : FiniteGaloisIntermediateField K L) : GrpCat.{w} :=
  GrpCat.of (actualFiniteWildSubgroup A K L Q E)

/-- Cardinality of the same subgroup is its existing actual wild order. -/
theorem actualFiniteWildSubgroup_card (E : FiniteGaloisIntermediateField K L) :
    Nat.card (actualFiniteWildSubgroup A K L Q E) = actualFiniteStageWildOrder A K L Q E := by
  have dB : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact commAlgIdealWildSubgroup_card A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The same subgroup's index is the existing actual tame order. -/
theorem actualFiniteWildSubgroup_index (E : FiniteGaloisIntermediateField K L) :
    (actualFiniteWildSubgroup A K L Q E).index = actualFiniteStageTameOrder A K L Q E := by
  have dB : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact commAlgIdealWildSubgroup_index A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

omit [Q.IsMaximal] in
/-- Its intrinsic ambient inertia group is finite. -/
theorem actualFiniteStageInertiaGroup_finite (E : FiniteGaloisIntermediateField K L) :
    Finite (actualFiniteStageInertiaGroup A K L Q E).carrier := by
  have fG : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  exact commAlgIdealInertiaGroup_finite A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)

/-- The same actual finite wild subgroup is normal in intrinsic finite inertia. -/
theorem actualFiniteWildSubgroup_normal (E : FiniteGaloisIntermediateField K L) :
    (actualFiniteWildSubgroup A K L Q E).Normal := by
  have dB : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have fG : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  exact commAlgIdealWildSubgroup_normal A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

end EtaleFundamentalGroups.Inertia

end

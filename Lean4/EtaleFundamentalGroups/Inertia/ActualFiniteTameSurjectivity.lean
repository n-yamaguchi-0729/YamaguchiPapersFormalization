/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaSurjectivity
import EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameMorphism
import EtaleFundamentalGroups.Inertia.ActualFiniteRootsGroupMap
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import EtaleFundamentalGroups.Inertia.ActualFiniteTamePrimitiveRoots
import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCoprimeExactness
import EtaleFundamentalGroups.Inertia.ActualFiniteTameOrderTower
import EtaleFundamentalGroups.Inertia.ActualFiniteTameIndex
import EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

/-!
# Surjectivity of the actual finite tame coordinates

The finite canonical character is onto its full native root group. The
finite residue embedding preserves that full root group, and the actual
original inertia restriction is onto. Their SAME existing composite is
therefore surjective. The same finite primitive root also gives a primitive
root in the original ambient residue field.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsMaximal]
  (E : FiniteGaloisIntermediateField K L)

/-- Exactness of the native finite normalization supplies surjectivity of
the SAME actual finite canonical morphism. -/
theorem actualFiniteCanonicalTameMorphism_surjective :
    Function.Surjective (actualFiniteCanonicalTameMorphism A K L Q E).hom'.toFun := by
  have : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  have hcop : Nat.Coprime (actualFiniteStageTameOrder A K L Q E)
      ((finiteAbsoluteNormalizationPrime A K L Q E).ramificationIdx A /
        actualFiniteStageTameOrder A K L Q E) :=
    (actualFiniteStage_tame_arithmetic A K L Q E).2 (actualFiniteStageTameOrder A K L Q E)
      (actualFiniteStageTameOrder_isUnit A K L Q E)
  exact (commAlgCanonicalTameMorphism_exact_of_coprime A
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E) hcop).1

/-- The SAME actual finite residue-root embedding is onto the full root
group of the ambient residue field. -/
theorem actualFiniteRootsGroupMap_surjective :
    Function.Surjective (actualFiniteRootsGroupMap A K L Q E).hom'.toFun := by
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  have : NeZero (actualFiniteStageTameOrder A K L Q E) :=
    ⟨(actualFiniteStageTameOrder_pos A K L Q E).ne'⟩
  exact RamificationTheory.HilbertRamification.rootsGroupMap_surjective_of_primitiveRoot
    (actualFiniteNormalizationResidueMap A K L Q E) (actualFiniteStageTameOrder A K L Q E)
    (actualFiniteStageTameOrder_exists_primitiveRoot_finiteResidue A K L Q E)

/-- Every ambient tame root is the value of the SAME actual finite
coordinate on an original inertia element. -/
theorem actualFiniteTameCoordinate_surjective :
    Function.Surjective (actualFiniteTameCoordinate A K L Q E).hom'.toFun := by
  exact (actualFiniteRootsGroupMap_surjective A K L Q E).comp
    ((actualFiniteCanonicalTameMorphism_surjective A K L Q E).comp
      (actualFiniteInertiaRestriction_surjective (hQ := hQ.isPrime) A K L Q E))

end EtaleFundamentalGroups.Inertia

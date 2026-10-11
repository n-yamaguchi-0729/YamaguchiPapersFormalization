/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import EtaleFundamentalGroups.Inertia.CommAlgIdealTamePrimitiveRoots
import EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive roots of actual finite tame degrees

The literal finite normalization supplies a primitive root in its own
residue field. The existing residue embedding transports it into the
original ambient residue field.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
  (E : FiniteGaloisIntermediateField K L)

/-- The finite residue field itself contains a primitive root of the SAME
actual finite tame degree. No ambient residue field is opened here. -/
theorem actualFiniteStageTameOrder_exists_primitiveRoot_finiteResidue :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∃ ζ : (finiteAbsoluteNormalizationPrime A K L Q E).ResidueField,
      IsPrimitiveRoot ζ (actualFiniteStageTameOrder A K L Q E) := by
  intro qPrime
  have : IsDedekindDomain (finiteAbsoluteNormalizationAlgebra A K L E).carrier :=
    finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  have : Finite ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  exact commAlgIdealTameOrder_exists_primitiveRoot A
    (finiteAbsoluteNormalizationAlgebra A K L E) (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

/-- The literal ambient residue field contains a primitive root of every
actual finite tame degree. -/
theorem actualFiniteStageTameOrder_exists_primitiveRoot :
    ∃ ζ : Q.ResidueField, IsPrimitiveRoot ζ (actualFiniteStageTameOrder A K L Q E) := by
  have : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  obtain ⟨ζ, hζ⟩ := actualFiniteStageTameOrder_exists_primitiveRoot_finiteResidue A K L Q E
  exact ⟨(actualFiniteNormalizationResidueMap A K L Q E).toFun ζ,
    hζ.map_of_injective (actualFiniteNormalizationResidueMap A K L Q E).injective⟩

end EtaleFundamentalGroups.Inertia

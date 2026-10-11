/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteTameIndex
import EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import ProCGroups.InverseSystems.CofinalityAndDensity

/-!
# The actual finite-order roots system at the original absolute prime

The index subset is the literal range of the constructed finite-stage tame
indices. The coefficients are the original maximal quotient of the absolute
normalization. Thus both the index set and the restricted roots system are
computed from the original DVR, separable closure and chosen maximal prime.

No cofinality or character comparison is part of the definition; those must
be proved from the actual uniformizer-radical stages.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups.InverseSystems

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

/-- The actual finite tame orders, with their constructed invertibility
proofs in the original residue field. -/
def actualFiniteTameDegreeSet : Set (InvertibleExponent (IsLocalRing.ResidueField A)) :=
  Set.range (actualFiniteStageTameIndex A K Ω Q)

/-- The actual roots system over finite tame orders at the original
absolute normalization prime. -/
def actualFiniteTameRootsSystem :
    InverseSystem.{0, w} (I := actualFiniteTameDegreeSet A K Ω Q) :=
  (primeToRootsSystem (IsLocalRing.ResidueField A)
    ((normalizationCommAlgCat A Ω) ⧸ Q)).restrict (actualFiniteTameDegreeSet A K Ω Q)

end EtaleFundamentalGroups.Inertia

end

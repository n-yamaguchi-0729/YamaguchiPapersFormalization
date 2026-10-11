/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import EtaleFundamentalGroups.Inertia.ActualFiniteTameGroups
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.NormalizationRootsGroup
import SchemeTheory.Normalization.SubalgebraPreimage
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

/-!
# Finite residue roots in the ambient field

Constructs the homomorphism from finite tame-degree residue roots into roots of the same degree
in the original ambient residue field.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory RamificationTheory.HilbertRamification

universe u v w

/-- The actual tame-degree root group at a finite prime embeds into the
same-degree root group of the original ambient residue field. -/
def actualFiniteRootsGroupMap
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    actualFiniteStageTameRootsGroup A K L Q E ⟶
      normalizationRootsGroup A L Q (actualFiniteStageTameOrder A K L Q E) := by
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact rootsGroupMap (actualFiniteNormalizationResidueMap A K L Q E)
    (actualFiniteStageTameOrder A K L Q E)

end EtaleFundamentalGroups.Inertia

end

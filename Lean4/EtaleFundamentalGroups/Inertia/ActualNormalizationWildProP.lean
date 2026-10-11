/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualNormalizationWildGroup
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildTopology
import EtaleFundamentalGroups.Inertia.ActualFiniteWildProperties
import ProCGroups.ProC.ProPOfFiniteEmbedding
import ProCGroups.ProC.InverseLimits.Predicates
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The independently defined original wild group is pro-p

Its actual finite wild coordinates are p-groups, locally constant and
jointly faithful. Closed-product permanence for pro-p groups therefore
applies to the SAME original wild subgroup in its inherited topology.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Original wild inertia has a basis of open normal subgroups with finite
p-group quotients in positive characteristic of the original base residue field. -/
theorem actualNormalizationWildGroup_hasPGroupOpenNormalBasis
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    ProCGroups.ProC.HasPGroupOpenNormalBasis p (actualNormalizationWildGroup A K L Q).carrier := by
  have hcompact : CompactSpace (actualNormalizationWildGroup A K L Q).carrier :=
    actualNormalizationWildGroup_compactSpace A K L Q
  exact ProCGroups.ProC.hasPGroupOpenNormalBasis_of_finiteCoordinates p
    (actualNormalizationWildGroup A K L Q)
    (FiniteGaloisIntermediateField K L) (actualFiniteWildFiniteGroup A K L Q)
    (fun E => (actualNormalizationWildRestriction A K L Q E).hom')
    (actualNormalizationWildRestriction_isLocallyConstant A K L Q)
    (actualNormalizationWildRestriction_jointly_injective A K L Q)
    (fun E => actualFiniteWildSubgroup_isPGroup_of_baseResidue_charP A K L Q E p)

end EtaleFundamentalGroups.Inertia

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaFaithful
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualOrdinaryFaithfulness
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Sigma-abelianization-faithfulness implies ordinary faithfulness
-/

namespace ProCGroups.FiniteStepSolvableQuotients

universe u

/-- The stronger Sigma condition implies the ordinary condition on all
open subgroups and all their open normal subgroups. -/
theorem IsSigmaAbFaithful.isAbFaithful {sigma : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : IsSigmaAbFaithful sigma G) : IsAbFaithful G := by
  intro H N
  have : CompactSpace (H : Subgroup G) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  exact ProC.quotientConjugationTopologicalAbelianizationMap_injective_of_residual
    (FiniteGroupClass.sigmaGroup_fullFormation sigma)
    (N : Subgroup (H : Subgroup G)) N.isClosed (hG H N)

end ProCGroups.FiniteStepSolvableQuotients

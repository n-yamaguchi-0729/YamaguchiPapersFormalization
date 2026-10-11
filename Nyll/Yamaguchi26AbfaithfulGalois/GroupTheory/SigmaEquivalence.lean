/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaFaithful
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Transport of Sigma-ab-faithfulness

A topological group equivalence identifies every open layer and its normal
quotient action on the actual residual abelianization.
-/

namespace ProCGroups.FiniteStepSolvableQuotients
open ProCGroups.ProC
universe u

/-- Sigma-ab-faithfulness is invariant under topological group equivalences. -/
theorem IsSigmaAbFaithful.of_continuousMulEquiv
    {G H : Type u} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    {sigma : Set ℕ} (e : G ≃ₜ* H) (hH : IsSigmaAbFaithful sigma H) :
    IsSigmaAbFaithful sigma G := by
  intro U
  have : CompactSpace (U : Subgroup G) := U.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let V : OpenSubgroup H :=
    { toSubgroup := (U : Subgroup G).map e.toMulEquiv.toMonoidHom
      isOpen' := e.toHomeomorph.isOpenMap U U.isOpen }
  have : CompactSpace (V : Subgroup H) := V.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let f : (U : Subgroup G) ≃* (V : Subgroup H) :=
    (U : Subgroup G).equivMapOfInjective e.toMulEquiv.toMonoidHom e.injective
  have hf : Continuous f := (e.continuous_toFun.comp continuous_subtype_val).subtype_mk _
  let t : (U : Subgroup G) ≃ₜ* (V : Subgroup H) :=
    { f with
      continuous_toFun := hf
      continuous_invFun :=
        (f.toEquiv.toHomeomorphOfContinuousClosed hf hf.isClosedMap).continuous_invFun }
  intro N
  let M : OpenNormalSubgroup (V : Subgroup H) :=
    ProC.OpenNormalSubgroup.map (t : (U : Subgroup G) →ₜ* (V : Subgroup H))
      t.toHomeomorph.isOpenMap t.surjective N
  exact (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) t
    (N : Subgroup (U : Subgroup G)) N.isClosed).mp (hH V M)

end ProCGroups.FiniteStepSolvableQuotients

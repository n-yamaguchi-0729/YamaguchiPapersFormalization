/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.SigmaCentralizers

/-! # Lemma 6.3: centralizers modulo the maximal abelian pro-Σ kernel

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Lemma 6.3.
-/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups ProCGroups.ProC ProCGroups.FiniteStepSolvableQuotients
universe u

/-- Centralizers of open subgroups containing `D` lie in the image of `D`. -/
theorem centralizer_criterion_6_3 {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (hG : IsSigmaAbFaithful sigma G)
    (D : ClosedSubgroup G) [(D : Subgroup G).Normal]
    (H : OpenSubgroup G) (hDH : (D : Subgroup G) ≤ (H : Subgroup G)) :
    Subgroup.centralizer ((H : Subgroup G).map (QuotientGroup.mk' (sigmaResidualKernel sigma D)) :
      Set (G ⧸ sigmaResidualKernel sigma D)) ≤
        (D : Subgroup G).map (QuotientGroup.mk' (sigmaResidualKernel sigma D)) := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (sigmaResidualKernel sigma D) z
  have hxD : x ∈ (D : Subgroup G) := by
    by_contra hxD
    let V := ProCGroups.ProC.OpenNormalSubgroup.normalCore H
    obtain ⟨W, hWV, hxW⟩ := exists_openNormalSubgroup_le_not_mem_sup_closedSubgroup D hxD V
    have hWH : (W : Subgroup G) ≤ (H : Subgroup G) :=
      hWV.trans (ProCGroups.ProC.OpenNormalSubgroup.normalCore_le H)
    let N := openNormalSubgroup_sup_normal (D : Subgroup G) W
    apply hxW
    exact sigmaQuotient_mem_openNormal_of_centralizes sigma hG D N le_sup_left x
      (Subgroup.centralizer_le (Subgroup.map_mono (sup_le hDH hWH)) hz)
  exact ⟨x, hxD, rfl⟩

end Yamaguchi26AbfaithfulGalois

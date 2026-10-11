/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.SigmaKernel
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaFaithful
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers in sigma-residual quotients

Sigma-abelian faithfulness makes the action on an open normal subgroup
injective. An element centralizing that subgroup in a sigma-residual
quotient consequently belongs to the subgroup.
-/

open scoped commutatorElement

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups ProCGroups.ProC ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients
universe u

/-- Faithfulness on an open normal subgroup, with ambient group `G`. -/
theorem sigmaFaithful_openNormal_action {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (hG : IsSigmaAbFaithful sigma G) (N : OpenNormalSubgroup G) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.sigmaGroup_fullFormation sigma) (N : Subgroup G) N.isClosed) := by
  let H : OpenSubgroup G := ⊤
  have : CompactSpace (H : Subgroup G) := H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let e : G ≃ₜ* (H : Subgroup G) :=
    { toMulEquiv := Subgroup.topEquiv.symm
      continuous_toFun := continuous_id.subtype_mk (fun _ => Subgroup.mem_top _)
      continuous_invFun := continuous_subtype_val }
  let Nmap : OpenNormalSubgroup (H : Subgroup G) :=
    ProCGroups.ProC.OpenNormalSubgroup.map
      (ContinuousMonoidHom.toContinuousMonoidHom e) e.toHomeomorph.isOpenMap e.surjective N
  exact (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) e (N : Subgroup G) N.isClosed).mp (hG H Nmap)

theorem sigmaQuotient_mem_openNormal_of_centralizes {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (hG : IsSigmaAbFaithful sigma G)
    (D : ClosedSubgroup G) [(D : Subgroup G).Normal]
    (N : OpenNormalSubgroup G) (hDN : (D : Subgroup G) ≤ (N : Subgroup G))
    (x : G) (hx : QuotientGroup.mk' (sigmaResidualKernel sigma D) x ∈
      Subgroup.centralizer ((N : Subgroup G).map (QuotientGroup.mk' (sigmaResidualKernel sigma D)) :
        Set (G ⧸ sigmaResidualKernel sigma D))) : x ∈ (N : Subgroup G) := by
  have : CompactSpace (N : Subgroup G) := N.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  by_contra hxn
  apply (residualAbelianizationQuotientConjugation_injective_iff
    (FiniteGroupClass.sigmaGroup_fullFormation sigma) (N : Subgroup G) N.isClosed).mp
      (sigmaFaithful_openNormal_action sigma hG N) x hxn
  apply MulEquiv.ext
  intro a
  obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk _ a
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have hc : ⁅x, (n : G)⁆ ∈ sigmaResidualKernel sigma D := by
    apply (QuotientGroup.eq_one_iff (N := sigmaResidualKernel sigma D) _).mp
    change QuotientGroup.mk' (sigmaResidualKernel sigma D) ⁅x, (n : G)⁆ = 1
    rw [map_commutatorElement]
    exact Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hx _ ⟨n, n.property, rfl⟩
  have hcN := sigmaResidualKernel_mono sigma D ⟨(N : Subgroup G), N.isClosed⟩ hDN hc
  have heq := (mem_sigmaResidualKernel_iff sigma ⟨(N : Subgroup G), N.isClosed⟩
    (MulAut.conjNormal x n * n⁻¹)).mp hcN
  rw [map_mul, map_inv, mul_inv_eq_one] at heq
  change TopologicalAbelianization.congr _
    (TopologicalAbelianization.mk _ (QuotientGroup.mk' _ n)) = _
  rw [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk]
  exact heq

end Yamaguchi26AbfaithfulGalois

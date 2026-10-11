/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.SigmaKernel
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Fixed primary classes in sigma quotients

Centralizing classes in sigma-residual quotients project to fixed
primary classes for primes in sigma. Vanishing of those fixed classes
forces the centralizing quotient class to be trivial.
-/

open scoped commutatorElement
namespace Yamaguchi26AbfaithfulGalois
open ProCGroups ProCGroups.Abelian ProCGroups.ProC
universe u

theorem primaryProjection_mem_fixed_of_sigmaQuotient_centralizes {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) [(D : Subgroup G).Normal]
    (H : Subgroup G) (d : (D : Subgroup G))
    (hd : QuotientGroup.mk' (sigmaResidualKernel sigma D) (d : G) ∈
      Subgroup.centralizer (H.map (QuotientGroup.mk' (sigmaResidualKernel sigma D)) :
        Set (G ⧸ sigmaResidualKernel sigma D)))
    (p : ℕ) [Fact p.Prime] (hp : p ∈ sigma) :
    QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p)
      (TopologicalAbelianization (D : Subgroup G)))
        (TopologicalAbelianization.mk (D : Subgroup G) d) ∈
          primaryFixedSubgroup p (D : Subgroup G) D.isClosed' H := by
  intro h
  have hc : ⁅(h : G), (d : G)⁆ ∈ sigmaResidualKernel sigma D := by
    apply (QuotientGroup.eq_one_iff (N := sigmaResidualKernel sigma D) _).mp
    change QuotientGroup.mk' (sigmaResidualKernel sigma D) ⁅(h : G), (d : G)⁆ = 1
    rw [map_commutatorElement]
    exact Subgroup.mem_centralizer_iff_commutator_eq_one.mp hd _ ⟨h, h.property, rfl⟩
  have heq := primaryProjection_eq_one_of_mem_sigmaResidualKernel sigma D
    (MulAut.conjNormal (h : G) d * d⁻¹) hc p hp
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at heq
  exact heq

theorem sigmaQuotient_eq_one_of_primaryFixed_eq_bot {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) [(D : Subgroup G).Normal]
    (H : Subgroup G)
    (hfixed : ∀ (p : ℕ) [Fact p.Prime], p ∈ sigma →
      Nontrivial (PrimaryAbelianization p (D : Subgroup G)) →
        primaryFixedSubgroup p (D : Subgroup G) D.isClosed' H = ⊥)
    (d : (D : Subgroup G))
    (hd : QuotientGroup.mk' (sigmaResidualKernel sigma D) (d : G) ∈
      Subgroup.centralizer (H.map (QuotientGroup.mk' (sigmaResidualKernel sigma D)) :
        Set (G ⧸ sigmaResidualKernel sigma D))) :
    QuotientGroup.mk' (sigmaResidualKernel sigma D) (d : G) = 1 := by
  apply (QuotientGroup.eq_one_iff (N := sigmaResidualKernel sigma D) _).mpr
  apply mem_sigmaResidualKernel_of_primaryProjections sigma D d
  intro p _ hp
  cases subsingleton_or_nontrivial (PrimaryAbelianization p (D : Subgroup G)) with
  | inl h => exact h.elim _ _
  | inr h =>
      exact Subgroup.mem_bot.mp ((hfixed p hp h) ▸
        primaryProjection_mem_fixed_of_sigmaQuotient_centralizes sigma D H d hd p hp)

end Yamaguchi26AbfaithfulGalois

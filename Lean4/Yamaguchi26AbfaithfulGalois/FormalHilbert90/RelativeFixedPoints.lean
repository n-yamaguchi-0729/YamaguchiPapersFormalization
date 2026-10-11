/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import ProCGroups.Abelian.SubgroupCommutator
import ProCGroups.Abelian.PrimaryDetection
import ProCGroups.GroupTheory.RelativeQuotientCentralizers

/-!
# Relative derived quotients and fixed primary classes

Centralizing classes in relative derived quotients yield fixed primary
abelianization classes. Vanishing of these fixed classes forces the
centralizing quotient class to be trivial.
-/

open scoped commutatorElement
namespace Yamaguchi26AbfaithfulGalois
open ProCGroups.FiniteStepSolvableQuotients ProCGroups.Abelian ProCGroups.ProC
universe u

theorem relativeDerived_mem_iff
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) (hD : IsClosed (D : Set G)) (d : D) :
    (d : G) ∈ relativeDerived D ↔ TopologicalAbelianization.mk D d = 1 := by
  rw [show relativeDerived D = (Subgroup.closedCommutator D).map D.subtype from
    (map_closedCommutator_subtype D hD).symm]
  constructor
  · rintro ⟨e, he, hed⟩
    have : e = d := Subtype.ext hed
    subst e
    exact TopologicalAbelianization.mk_eq_one_iff.mpr he
  · intro hd
    exact ⟨d, TopologicalAbelianization.mk_eq_one_iff.mp hd, rfl⟩

theorem relativeDerived_quotient_mem_openNormal_of_centralizes
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) [D.Normal]
    (N : OpenNormalSubgroup G) (hDN : D ≤ (N : Subgroup G))
    (hN : Function.Injective
      (quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G))))
    (x : G)
    (hx : QuotientGroup.mk' (relativeDerived D) x ∈
      Subgroup.centralizer (((N : Subgroup G).map
        (QuotientGroup.mk' (relativeDerived D))) : Set (RelativeDerivedQuotient D))) :
    x ∈ (N : Subgroup G) := by
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup G)) x).mp
  apply hN
  rw [map_one]
  apply quotientConjugationTopologicalAbelianizationMap_mk_eq_one_iff.mpr
  intro n
  have hc : ⁅x, (n : G)⁆ ∈ relativeDerived D := by
    apply (QuotientGroup.eq_one_iff (N := relativeDerived D) _).mp
    change QuotientGroup.mk' (relativeDerived D) ⁅x, (n : G)⁆ = 1
    rw [map_commutatorElement]
    exact Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hx _
      ⟨n, n.property, rfl⟩
  have hle : relativeDerived D ≤ relativeDerived (N : Subgroup G) :=
    Subgroup.topologicalClosure_mono (Subgroup.commutator_mono hDN hDN)
  have hmem : (((MulAut.conjNormal x) n) * n⁻¹ : (N : Subgroup G)) ∈
      Subgroup.closedCommutator (N : Subgroup G) := by
    apply TopologicalAbelianization.mk_eq_one_iff.mp
    apply (relativeDerived_mem_iff (N : Subgroup G) N.isClosed _).mp
    exact hle hc
  exact hmem

theorem primaryAbelianization_mk_mem_fixed_of_quotient_centralizes
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (H : Subgroup G) (d : D)
    (hd : QuotientGroup.mk' (relativeDerived D) (d : G) ∈
      Subgroup.centralizer (H.map (QuotientGroup.mk' (relativeDerived D)) :
        Set (RelativeDerivedQuotient D)))
    (p : ℕ) [Fact p.Prime] :
    QuotientGroup.mk' (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup p)
      (TopologicalAbelianization D)) (TopologicalAbelianization.mk D d) ∈
      primaryFixedSubgroup p D hD H := by
  intro h
  have hc : ⁅(h : G), (d : G)⁆ ∈ relativeDerived D := by
    apply (QuotientGroup.eq_one_iff (N := relativeDerived D) _).mp
    change QuotientGroup.mk' (relativeDerived D) ⁅(h : G), (d : G)⁆ = 1
    rw [map_commutatorElement]
    exact Subgroup.mem_centralizer_iff_commutator_eq_one.mp hd _
      ⟨h, h.property, rfl⟩
  have heq : TopologicalAbelianization.mk D ((MulAut.conjNormal (h : G)) d) =
      TopologicalAbelianization.mk D d := by
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact (relativeDerived_mem_iff D hD _).mp hc
  change QuotientGroup.mk' _ (TopologicalAbelianization.mk D ((MulAut.conjNormal (h : G)) d)) =
    QuotientGroup.mk' _ (TopologicalAbelianization.mk D d)
  exact congrArg (QuotientGroup.mk' _) heq

theorem relativeDerived_quotient_eq_one_of_primaryFixed_eq_bot
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (H : Subgroup G)
    (hfixed : ∀ (p : ℕ) [Fact p.Prime],
      Nontrivial (PrimaryAbelianization p D) → primaryFixedSubgroup p D hD H = ⊥)
    (d : D)
    (hd : QuotientGroup.mk' (relativeDerived D) (d : G) ∈
      Subgroup.centralizer (H.map (QuotientGroup.mk' (relativeDerived D)) :
        Set (RelativeDerivedQuotient D))) :
    QuotientGroup.mk' (relativeDerived D) (d : G) = 1 := by
  apply (QuotientGroup.eq_one_iff (N := relativeDerived D) _).mpr
  apply (relativeDerived_mem_iff D hD d).mpr
  have : CompactSpace D := hD.isClosedEmbedding_subtypeVal.compactSpace
  have : TotallyDisconnectedSpace (TopologicalAbelianization D) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator D) (Subgroup.isClosed_closedCommutator D)
  apply eq_one_of_forall_primaryQuotient
  intro p _
  cases subsingleton_or_nontrivial (PrimaryAbelianization p D) with
  | inl h => exact h.elim _ _
  | inr h =>
      exact Subgroup.mem_bot.mp ((hfixed p h) ▸
        primaryAbelianization_mk_mem_fixed_of_quotient_centralizes D hD H d hd p)

end Yamaguchi26AbfaithfulGalois

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.OrientedInvariants
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.RelativeFixedPoints
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SlimnessAndTorsion
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Relative center-freeness criterion

The earlier all-primes relative criterion, retained in the foundation layer.
The current Σ-quotient theorem is `Theorem6Dot4RelativeCriterion.lean`.
The quotient is the actual `G/[D,D]`, with closed commutator subgroup.
The orientation hypothesis ranges only over primes with nontrivial
primary abelianization of `D`.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients

universe u

theorem relative_centerfree_and_slim_criterion
    (G : ProfiniteGrp.{u})
    (D : Subgroup G) [D.Normal]
    (hDclosed : IsClosed (D : Set G)) (hDderived : D ≤ topDerivedTop G 1)
    (hFaithful : ∀ N : OpenNormalSubgroup G,
      D ≤ (N : Subgroup G) →
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := G) (N := (N : Subgroup G))))
    (hOrient : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      Nontrivial (PrimaryAbelianization ℓ D) →
        ∃ θ : Orientation ℓ G, RelativeFormalHilbert90 D θ) :
    Subgroup.center (RelativeDerivedQuotient D) = ⊥ ∧
      ((∀ (ℓ : ℕ) [Fact ℓ.Prime],
        Nontrivial (PrimaryAbelianization ℓ D) →
          ∃ θ : Orientation ℓ G,
            RelativeFormalHilbert90 D θ ∧ Set.Infinite (Set.range θ)) →
        IsSlim (RelativeDerivedQuotient D)) := by
  have hDθ {ℓ : ℕ} [Fact ℓ.Prime] (θ : Orientation ℓ G) :
      D ≤ θ.toMonoidHom.ker := by
    intro d hd
    change θ d = 1
    have hdcomm : d ∈ Subgroup.closedCommutator G := by
      simpa only [topDerivedTop, closedDerivedSeries_top_one_eq_closedCommutator] using
        hDderived hd
    rw [← TopologicalAbelianization.lift_apply_mk θ d,
      TopologicalAbelianization.mk_eq_one_iff.mpr hdcomm, map_one]
  let q := QuotientGroup.mk' (relativeDerived D)
  have hf (N : OpenNormalSubgroup G) (hDN : D ≤ (N : Subgroup G)) (x : G)
      (hx : q x ∈ Subgroup.centralizer ((N : Subgroup G).map q : Set (RelativeDerivedQuotient D))) :
      x ∈ (N : Subgroup G) :=
    relativeDerived_quotient_mem_openNormal_of_centralizes D N hDN (hFaithful N hDN) x hx
  constructor
  · apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (relativeDerived D) z
    have hxD : x ∈ D := by
      apply ProCGroups.ProC.mem_closedSubgroup_of_forall_openNormal_sup ⟨D, hDclosed⟩
      intro U
      exact hf (ProCGroups.ProC.openNormalSubgroup_sup_normal D U) le_sup_left x
        (Subgroup.center_le_centralizer _ hz)
    apply relativeDerived_quotient_eq_one_of_primaryFixed_eq_bot D hDclosed
      (⊤ : Subgroup G) (d := ⟨x, hxD⟩)
    · intro ℓ _ hNontrivial
      obtain ⟨θ, hLift⟩ := hOrient ℓ hNontrivial
      exact (oriented_invariants G D hDclosed θ (hDθ θ) hLift).2.2.1 hDderived
    · exact Subgroup.center_le_centralizer _ hz
  · intro hInfinite U
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (relativeDerived D) z
    let V : OpenSubgroup G := OpenSubgroup.comap q QuotientGroup.continuous_mk U
    have hxV : q x ∈ Subgroup.centralizer ((V : Subgroup G).map q :
        Set (RelativeDerivedQuotient D)) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hz (q v) hv
    apply ProCGroups.quotient_eq_one_of_relative_fixedPoints q
      (QuotientGroup.mk'_surjective _) D hDclosed hf _ V x hxV
    intro H d hd hfixed
    apply relativeDerived_quotient_eq_one_of_primaryFixed_eq_bot D hDclosed
      (H : Subgroup G) (d := ⟨d, hd⟩) _ hfixed
    intro ℓ _ hNontrivial
    obtain ⟨θ, hLift, hImage⟩ := hInfinite ℓ hNontrivial
    exact (oriented_invariants G D hDclosed θ (hDθ θ) hLift).2.2.2 hImage H


end Yamaguchi26AbfaithfulGalois

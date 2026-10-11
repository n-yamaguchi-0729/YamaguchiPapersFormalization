/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot2IntegralInvariants
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot3CentralizerCriterion
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.SigmaFixedPoints
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SlimnessAndTorsion
import Nyll.ProCGroups.GroupTheory.RelativeQuotientCentralizers

/-! # Theorem 6.4: center-freeness and slimness of `G/R_Σ(D)`

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Theorem 6.4.
The previous criterion for `G/[D,D]`, requiring only relative Hilbert 90,
is retained in `FormalHilbert90/RelativeDerivedCriterion.lean`.
-/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients
universe u

theorem relative_centerfree_and_slim_criterion_6_4
    (sigma : Set ℕ) (G : ProfiniteGrp.{u}) (hG : IsSigmaAbFaithful sigma G)
    (D : ClosedSubgroup G) [(D : Subgroup G).Normal]
    (hDderived : (D : Subgroup G) ≤ topDerivedTop G 1)
    (hOrient : ∀ (p : ℕ) [Fact p.Prime], p ∈ sigma →
      Nontrivial (PrimaryAbelianization p (D : Subgroup G)) →
        ∃ θ : Orientation p G, FormalHilbert90 θ) :
    Subgroup.center (G ⧸ sigmaResidualKernel sigma D) = ⊥ ∧
      ((∀ (p : ℕ) [Fact p.Prime], p ∈ sigma →
        Nontrivial (PrimaryAbelianization p (D : Subgroup G)) →
          ∃ θ : Orientation p G, FormalHilbert90 θ ∧ Set.Infinite (Set.range θ)) →
            IsSlim (G ⧸ sigmaResidualKernel sigma D)) := by
  let q := QuotientGroup.mk' (sigmaResidualKernel sigma D)
  constructor
  · apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    have hzD := centralizer_criterion_6_3 sigma hG D ⊤ le_top
      (Subgroup.center_le_centralizer _ hz)
    obtain ⟨d, hd, rfl⟩ := hzD
    refine sigmaQuotient_eq_one_of_primaryFixed_eq_bot sigma D (⊤ : Subgroup G) ?_ ⟨d, hd⟩ ?_
    · intro p _ hp hNontrivial
      obtain ⟨θ, hθ⟩ := hOrient p hp hNontrivial
      exact (integral_invariants_6_2 G (D : Subgroup G) D.isClosed' hDderived θ hθ).1
    · exact Subgroup.center_le_centralizer _ hz
  · intro hInfinite U
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (sigmaResidualKernel sigma D) z
    let V : OpenSubgroup G := OpenSubgroup.comap q QuotientGroup.continuous_mk U
    have hxV : q x ∈ Subgroup.centralizer ((V : Subgroup G).map q :
        Set (G ⧸ sigmaResidualKernel sigma D)) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hz (q v) hv
    apply ProCGroups.quotient_eq_one_of_relative_fixedPoints q
      (QuotientGroup.mk'_surjective _) (D : Subgroup G) D.isClosed'
      (fun N hDN x hx => sigmaQuotient_mem_openNormal_of_centralizes sigma hG D N hDN x hx)
      _ V x hxV
    intro H d hd hfixed
    apply sigmaQuotient_eq_one_of_primaryFixed_eq_bot sigma D (H : Subgroup G) _ ⟨d, hd⟩ hfixed
    intro p _ hp hNontrivial
    obtain ⟨θ, hθ, hImage⟩ := hInfinite p hp hNontrivial
    exact (integral_invariants_6_2 G (D : Subgroup G) D.isClosed' hDderived θ hθ).2 hImage H

end Yamaguchi26AbfaithfulGalois

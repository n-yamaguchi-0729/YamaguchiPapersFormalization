/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.FixedInclusion
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.OrientedConsequences
import ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Proposition: oriented invariants

The stronger oriented-invariants theorem retained from the earlier manuscript.
It implies current Lemma 6.2 and additionally proves torsion-freeness and
injectivity of the fixed-inclusion map.
The fixed-point assertions use the natural map between residual pro-ℓ
quotients of topological abelianizations.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients ProCGroups.ProC

universe u

theorem oriented_invariants
    {ℓ : ℕ} [Fact ℓ.Prime]
    (G : ProfiniteGrp.{u})
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ) :
    IsMulTorsionFree (PrimaryAbelianization ℓ D) ∧
      Function.Injective
        (fun a : primaryFixedSubgroup ℓ D hDclosed (⊤ : Subgroup G) =>
          primaryInclusionMap ℓ D hDclosed (a : PrimaryAbelianization ℓ D)) ∧
      (D ≤ topDerivedTop G 1 →
        primaryFixedSubgroup ℓ D hDclosed (⊤ : Subgroup G) = ⊥) ∧
      (Set.Infinite (Set.range θ) →
        ∀ H : OpenSubgroup G,
          primaryFixedSubgroup ℓ D hDclosed (H : Subgroup G) = ⊥) := by
  have hMain :
      IsMulTorsionFree (PrimaryAbelianization ℓ D) ∧
        Function.Injective
          (fun a : primaryFixedSubgroup ℓ D hDclosed (⊤ : Subgroup G) =>
            primaryInclusionMap ℓ D hDclosed (a : PrimaryAbelianization ℓ D)) ∧
        (Set.Infinite (Set.range θ) →
          ∀ H : OpenSubgroup G,
            primaryFixedSubgroup ℓ D hDclosed (H : Subgroup G) = ⊥) := by
    exact ⟨primaryAbelianization_isMulTorsionFree D hDclosed θ hDθ hLift,
      primaryInclusionMap_injective_on_fixed D hDclosed θ hDθ hLift,
      primaryFixedSubgroup_eq_bot_of_infinite_orientation D hDclosed θ hDθ hLift⟩
  rcases hMain with ⟨hTF, hInj, hInfinite⟩
  refine ⟨hTF, hInj, ?_, hInfinite⟩
  intro hDerived
  have hDcomm : D ≤ Subgroup.closedCommutator G := by
    simpa only [topDerivedTop, closedDerivedSeries_top_one_eq_closedCommutator] using hDerived
  have hAbZero (a : TopologicalAbelianization D) :
      abelianizationInclusion D a = 1 := by
    obtain ⟨d, rfl⟩ := TopologicalAbelianization.surjective_mk D a
    change TopologicalAbelianization.mk G (d : G) = 1
    exact TopologicalAbelianization.mk_eq_one_iff.mpr (hDcomm d.property)
  have hPrimaryZero (a : PrimaryAbelianization ℓ D) :
      primaryInclusionMap ℓ D hDclosed a = 1 := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
        (TopologicalAbelianization D)) a
    change QuotientGroup.mk'
      (proCResidualCore (ProCGroups.FiniteGroupClass.pGroup ℓ)
        (TopologicalAbelianization G)) (abelianizationInclusion D b) = 1
    rw [hAbZero b]
    exact map_one _
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have hEq : (⟨a, ha⟩ : primaryFixedSubgroup ℓ D hDclosed (⊤ : Subgroup G)) = 1 :=
    hInj (by simpa using hPrimaryZero a)
  exact congrArg Subtype.val hEq

end Yamaguchi26AbfaithfulGalois

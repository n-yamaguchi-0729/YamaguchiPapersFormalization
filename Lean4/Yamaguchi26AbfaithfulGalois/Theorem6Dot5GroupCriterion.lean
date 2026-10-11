/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.RelativeDerivedCriterion
import Yamaguchi26AbfaithfulGalois.GroupTheory.Faithful
import ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import ProCGroups.Topologies.OpenSubgroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Finite-step solvable quotients of an ab-faithful group

`AbfatifhulGalois.tex`, Corollary `cor:cf-group-criterion`.
Each orientation satisfies formal Hilbert 90 on every open subgroup.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u

theorem finiteStepSolvable_centerfree_and_slim_of_formalHilbert90
    (G : ProfiniteGrp.{u})
    (hG : IsAbFaithful G)
    (hOrient : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      ∃ θ : Orientation ℓ G, FormalHilbert90 θ) :
    (∀ m : ℕ, 2 ≤ m → Subgroup.center (MaxSolvQuot G m) = ⊥) ∧
      ((∀ (ℓ : ℕ) [Fact ℓ.Prime],
        ∃ θ : Orientation ℓ G,
          FormalHilbert90 θ ∧ Set.Infinite (Set.range θ)) →
        ∀ m : ℕ, 2 ≤ m → IsSlim (MaxSolvQuot G m)) := by
  have hFaithful (N : OpenNormalSubgroup G) :
      Function.Injective
        (ProCGroups.Abelian.quotientConjugationTopologicalAbelianizationMap
          (G := G) (N := (N : Subgroup G))) := by
    apply quotientConjAbelianization_injective_of_continuousMulEquiv_image
      (ProCGroups.OpenSubgroup.topContinuousMulEquiv G).symm N
    exact hG ⊤ _
  have hRelative (m : ℕ) (hm : 2 ≤ m) :
      Subgroup.center (MaxSolvQuot G m) = ⊥ ∧
        ((∀ (ℓ : ℕ) [Fact ℓ.Prime],
          ∃ θ : Orientation ℓ G,
            FormalHilbert90 θ ∧ Set.Infinite (Set.range θ)) →
          IsSlim (MaxSolvQuot G m)) := by
    let D : Subgroup G := topDerivedTop G (m - 1)
    have hDclosed : IsClosed (D : Set G) := by
      exact inferInstance
    have hDderived : D ≤ topDerivedTop G 1 :=
      topDerivedTop_antitone (by omega : 1 ≤ m - 1)
    have hOrientD : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
        Nontrivial (PrimaryAbelianization ℓ D) →
          ∃ θ : Orientation ℓ G, RelativeFormalHilbert90 D θ := by
      intro ℓ _ _
      obtain ⟨θ, hθ⟩ := hOrient ℓ
      exact ⟨θ, fun N _ n hn => hθ N.toOpenSubgroup n hn⟩
    have hResult := relative_centerfree_and_slim_criterion G D hDclosed
      hDderived (fun N _ => hFaithful N) hOrientD
    have hIndex : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
    have hCenter : Subgroup.center (MaxSolvQuot G m) = ⊥ := by
      have hCenter' : Subgroup.center (MaxSolvQuot G (m - 1 + 1)) = ⊥ := hResult.1
      exact (congrArg (fun k : ℕ => Subgroup.center (MaxSolvQuot G k) = ⊥)
        hIndex).mp hCenter'
    refine ⟨hCenter, ?_⟩
    intro hInfinite
    have hSlim : IsSlim (RelativeDerivedQuotient D) := hResult.2 (by
      intro ℓ _ _
      obtain ⟨θ, hθ, hθInfinite⟩ := hInfinite ℓ
      exact ⟨θ, (fun N _ n hn => hθ N.toOpenSubgroup n hn), hθInfinite⟩)
    have hSlim' : IsSlim (MaxSolvQuot G (m - 1 + 1)) := hSlim
    exact (congrArg (fun k : ℕ => IsSlim (MaxSolvQuot G k)) hIndex).mp hSlim'
  exact ⟨fun m hm => (hRelative m hm).1,
    fun hInfinite m hm => (hRelative m hm).2 hInfinite⟩

end Yamaguchi26AbfaithfulGalois

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.OrientedInvariants

/-!
# Lemma 6.2: integral invariants

TeX label: `lem:cf-integral-invariants` in `AbfatifhulGalois.tex`.
The stronger torsion-freeness and fixed-inclusion theorem is retained in
`FormalHilbert90/OrientedInvariants.lean`.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Under formal Hilbert 90 the primary abelianization of a closed normal
subgroup of the closed derived group has no global invariants. An infinite
orientation also excludes invariants under every open subgroup. -/
theorem integral_invariants_6_2
    {ℓ : ℕ} [Fact ℓ.Prime] (G : ProfiniteGrp.{u})
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (hDderived : D ≤ topDerivedTop G 1)
    (θ : Orientation ℓ G) (hθ : FormalHilbert90 θ) :
    primaryFixedSubgroup ℓ D hDclosed (⊤ : Subgroup G) = ⊥ ∧
      (Set.Infinite (Set.range θ) → ∀ H : OpenSubgroup G,
        primaryFixedSubgroup ℓ D hDclosed (H : Subgroup G) = ⊥) := by
  have hDθ : D ≤ θ.toMonoidHom.ker := by
    intro d hd
    change θ d = 1
    have hdcomm : d ∈ Subgroup.closedCommutator G := by
      simpa only [topDerivedTop, closedDerivedSeries_top_one_eq_closedCommutator] using
        hDderived hd
    rw [← TopologicalAbelianization.lift_apply_mk θ d,
      TopologicalAbelianization.mk_eq_one_iff.mpr hdcomm, map_one]
  have hLift : RelativeFormalHilbert90 D θ :=
    fun N _ n hn => hθ N.toOpenSubgroup n hn
  have h := oriented_invariants G D hDclosed θ hDθ hLift
  exact ⟨h.2.2.1 hDderived, h.2.2.2⟩

end Yamaguchi26AbfaithfulGalois

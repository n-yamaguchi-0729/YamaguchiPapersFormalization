/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.Boundary
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot1BoundaryQuotient
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot2InertiaControl
import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Proposition 1.3: boundary invariance

For a horizontal effective Cartier divisor on a connected locally Noetherian
scheme regular along its support, assume that every component contains a normal
crossings point in every prime residue characteristic. The complement is connected,
and its inclusion induces an isomorphism on etale fundamental groups.

The isomorphism is required to agree with the homomorphism induced by the inclusion.
The proof applies Lemma 1.2 to every prime divisor of each finite inertia group's
order, then uses the kernel description in Lemma 1.1.

Source: [Yamaguchi, arXiv:2610.02948v1](https://arxiv.org/abs/2610.02948v1), Proposition 1.3.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- 命題 1.3。
水平境界の各成分に全ての素数についてその剰余標数の正規交差点があれば、
境界の補集合は連結であり、包含が étale 基本群の位相群同型を誘導する。 -/
theorem boundary_invariance_1_3
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport)
    (hnc : ∀ p : ℕ, p.Prime →
      D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent p) :
    ConnectedSpace D.1.supportComplement ∧
      ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
        (point : Spec (CommRingCat.of Ω) ⟶ D.1.supportComplement),
        ∃ e : π₁ᵉᵗ(point) ≃ₜ* π₁ᵉᵗ(point ≫ D.1.supportComplement.ι),
          ∀ g : π₁ᵉᵗ(point), e g = fundamentalGroupHom D.1.supportComplement.ι point g := by
  obtain ⟨hU, hquotient⟩ := boundary_quotient_finite_cover D hreg
  let _ : ConnectedSpace D.1.supportComplement := hU
  refine ⟨hU, ?_⟩
  intro Ω _ _ point
  have hunramified : ∀ (W : FiniteEtale D.1.supportComplement)
      (_hW : IsGalois W), IsBoundaryUnramified D W := by
    intro W hW E z hz
    have hcard : Nat.card (finiteCoverInertia D W E z) = 1 := by
      apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
      intro p hp
      exact finite_inertia_control D hhor hreg E p hp
        (hnc p hp E.val E.property) W hW z hz
    let _ : Subsingleton (finiteCoverInertia D W E z) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    apply le_antisymm ?_ bot_le
    intro σ hσ
    apply Subgroup.mem_bot.mpr
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨σ, hσ⟩ : finiteCoverInertia D W E z) 1)
  let f : π₁ᵉᵗ(point) →ₜ* π₁ᵉᵗ(point ≫ D.1.supportComplement.ι) :=
    fundamentalGroupHom D.1.supportComplement.ι point
  have hsurjective : Function.Surjective f := (hquotient Ω point).1
  have hkernel : f.toMonoidHom.ker = ⊥ := by
    change (fundamentalGroupHom D.1.supportComplement.ι point).toMonoidHom.ker = ⊥
    rw [(hquotient Ω point).2]
    apply le_antisymm ?_ bot_le
    intro g hg
    have hall : g ∈ ⨅ (W : FiniteEtale D.1.supportComplement)
        (hW : IsGalois W) (w : (fiber point).obj W),
        (letI : IsGalois W := hW
         galoisObjectQuotientMonoidHom (fiber point) π₁ᵉᵗ(point) W w).ker := by
      simp only [boundaryUnramifiedKernelIntersection, Subgroup.mem_iInf] at hg
      simp only [Subgroup.mem_iInf]
      intro W hW w
      exact hg W hW w (hunramified W hW)
    rw [iInf_galoisObjectQuotientMonoidHom_ker] at hall
    exact hall
  have hbijective : Function.Bijective f :=
    ⟨f.toMonoidHom.ker_eq_bot_iff.mp hkernel, hsurjective⟩
  refine ⟨ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    f.toMonoidHom f.continuous_toFun hbijective, ?_⟩
  intro g
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2_apply
    f.toMonoidHom f.continuous_toFun hbijective g

end Yamaguchi26SolvableCoverings

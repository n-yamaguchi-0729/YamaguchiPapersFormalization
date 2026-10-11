/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PureInseparableDescent
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.PurelyInseparablePullback
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# Perfection invariance

Purely inseparable extension of the constant field preserves connectedness
for an arbitrary scheme. The existing descent theorem for actual finite
étale covers then identifies the canonical fundamental-group homomorphism
with a topological group isomorphism after passage to a perfect closure.

The perfect-closure formulation uses exponential characteristic, so it also
includes characteristic zero, with exponential characteristic one.

Source: Stacks Project, Lemma 58.14.2, Tag 0BTW:
https://stacks.math.columbia.edu/tag/0BTW
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- A purely inseparable extension of the constant field preserves
connectedness without any finiteness assumptions on the scheme. -/
theorem connectedSpace_of_purelyInseparable_constant_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) [ConnectedSpace X] (f : X ⟶ Spec (.of k)) :
    ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) := by
  let p := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  have hp := EtaleFundamentalGroups.purelyInseparable_constantField_projection_properties
    k L X f
  let : IsIntegralHom p := hp.1
  let : UniversallyInjective p := hp.2.1
  let : Surjective p := hp.2.2
  let e : ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) ≃ X :=
    Equiv.ofBijective (fun x ↦ p x) ⟨p.injective, p.surjective⟩
  exact (e.toHomeomorphOfContinuousClosed p.continuous p.isClosedMap).connectedSpace_iff.mpr
    inferInstance

/-- Perfection preserves connectedness and makes the actual pullback map on
étale fundamental groups an isomorphism of topological groups. There are no
quasi-compactness, quasi-separatedness, Noetherian, or finite-type hypotheses. -/
@[stacks 0BTW]
theorem perfection_invariance
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (p : ℕ) [ExpChar k p] [ExpChar L p] [PerfectRing L p]
    [IsPerfectClosure (algebraMap k L) p]
    (X : Scheme.{u}) [ConnectedSpace X] (f : X ⟶ Spec (.of k)) :
    ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (ξ : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f),
        ∃ e : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ Limits.pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) f),
          ∀ a : π₁ᵉᵗ(ξ), e a = fundamentalGroupHom (Limits.pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) ξ a := by
  let : IsPurelyInseparable k L := IsPRadical.isPurelyInseparable k L p
  have hconn := connectedSpace_of_purelyInseparable_constant_extension k L X f
  refine ⟨hconn, ?_⟩
  intro Ω hΩ hsep ξ
  let : ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) := hconn
  let q := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f
  let : (pullback q).IsEquivalence :=
    pullback_isEquivalence_of_purelyInseparable_constant_extension k L X f
  refine ⟨fundamentalGroupEquivOfPullbackEquivalence q ξ, ?_⟩
  intro a
  exact fundamentalGroupEquivOfPullbackEquivalence_apply q ξ a

end AlgebraicGeometry.FiniteEtale

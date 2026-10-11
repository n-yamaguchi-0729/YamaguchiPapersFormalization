/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# exists rational Point enumeration of nat Card pullback eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_rationalPoint_enumeration_of_natCard_pullback_eq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem _root_.AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)} [LocallyOfFiniteType c₁] [LocallyOfFiniteType
      c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion
      i₂.1]
    (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s) :
    ∃ (p₁ : Fin s → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : Fin s → SchemeHomOver (𝟙 (Spec (.of
      κ))) c₂),
      (Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ)) ∧
      (∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) ∧
      ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
        ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base
          (IsLocalRing.closedPoint κ) := by
  classical
  let _ : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  let zc : pullback i₁.1 i₂.1 ⟶ Spec (.of κ) := pullback.fst i₁.1 i₂.1 ≫ c₁
  let _ : LocallyOfFiniteType zc := inferInstance
  let _ : JacobsonSpace ↥(pullback i₁.1 i₂.1) := LocallyOfFiniteType.jacobsonSpace zc
  let _ : DiscreteTopology ↥(pullback i₁.1 i₂.1) := inferInstance
  obtain ⟨e⟩ : Nonempty (↥(pullback i₁.1 i₂.1) ≃ Fin s) := by rw [← hs]; exact ⟨Finite.equivFin _⟩
  have hzc : ∀ z : ↥(pullback i₁.1 i₂.1), IsClosed ({z} : Set ↥(pullback i₁.1 i₂.1)) := fun z =>
    isClosed_discrete _
  let pt : Fin s → (Spec (.of κ) ⟶ pullback i₁.1 i₂.1) := fun r => pointOfClosedPoint zc (e.symm r)
    (hzc _)
  have hpt : ∀ r, pt r ≫ zc = 𝟙 _ := fun r => pointOfClosedPoint_comp zc _ _
  have hpt_apply : ∀ r, (pt r).base (IsLocalRing.closedPoint κ) = e.symm r := fun r =>
    pointOfClosedPoint_apply zc _ _ _
  have hzc₂ : pullback.snd i₁.1 i₂.1 ≫ c₂ = zc := by
    calc pullback.snd i₁.1 i₂.1 ≫ c₂ = pullback.snd i₁.1 i₂.1 ≫ (i₂.1 ≫ x) := by rw [i₂.2]
      _ = (pullback.fst i₁.1 i₂.1 ≫ i₁.1) ≫ x := by rw [← Category.assoc, pullback.condition]
      _ = pullback.fst i₁.1 i₂.1 ≫ c₁ := by rw [Category.assoc, i₁.2]
  refine ⟨fun r => ⟨pt r ≫ pullback.fst i₁.1 i₂.1, by rw [Category.assoc]; exact hpt r⟩,
    fun r => ⟨pt r ≫ pullback.snd i₁.1 i₂.1, by rw [Category.assoc, hzc₂]; exact hpt r⟩, ?_, ?_, ?_⟩
  · intro r r' hrr
    have hinjf := (pullback.fst i₁.1 i₂.1).isClosedEmbedding.injective
    change (pullback.fst i₁.1 i₂.1).base ((pt r).base (IsLocalRing.closedPoint κ)) =
      (pullback.fst i₁.1 i₂.1).base ((pt r').base (IsLocalRing.closedPoint κ)) at hrr
    rw [hpt_apply, hpt_apply] at hrr
    exact e.symm.injective (hinjf hrr)
  · intro r
    change (pt r ≫ pullback.fst i₁.1 i₂.1) ≫ i₁.1 = (pt r ≫ pullback.snd i₁.1 i₂.1) ≫ i₂.1
    simp only [Category.assoc, pullback.condition]
  · intro q₁ q₂ hq
    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁.1) (g := i₂.1) q₁ q₂
      hq
    refine ⟨e t, ?_, ?_⟩
    · change q₁ = (pullback.fst i₁.1 i₂.1).base ((pt (e t)).base (IsLocalRing.closedPoint κ))
      rw [hpt_apply, Equiv.symm_apply_apply, ht1]
    · change q₂ = (pullback.snd i₁.1 i₂.1).base ((pt (e t)).base (IsLocalRing.closedPoint κ))
      rw [hpt_apply, Equiv.symm_apply_apply, ht2]
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_rationalPoint_enumeration_of_natCard_pullback_eq
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_DescentAction_effective_of_isPullback_of_flat_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import AlgebraicCurves.Geometry.Descent.DescentAction

/-!
# Descent Action effective of is Pullback of flat surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Descent.Proofs
namespace DescentAction_effective_of_isPullback_of_flat_surjective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
    {S S' : Scheme.{u}} (s : S' ⟶ S) {X' : Scheme.{u}} {x' : X' ⟶ S'} (A : DescentAction s x')
    {Y : Scheme.{u}} (p : X' ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    (w : pullback.fst (x' ≫ s) s ≫ p = A.act ≫ p)
    (hR : IsPullback (pullback.fst (x' ≫ s) s) A.act p p)
    (f : Y ⟶ S) (hpf : p ≫ f = x' ≫ s) :
    ∃ (e : pullback f s ≅ X') (he : e.hom ≫ x' = pullback.snd f s),
      e.inv = pullback.lift p x' hpf ∧
      pullback.map (pullback.snd f s ≫ s) s (x' ≫ s) s e.hom (𝟙 S') (𝟙 S)
          (by rw [Category.comp_id, ← Category.assoc, he])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical s f).act ≫ e.hom := by
  set u : X' ⟶ pullback f s := pullback.lift p x' hpf
  have hu₁ : u ≫ pullback.fst f s = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd f s = x' := pullback.lift_snd _ _ _
  let c : pullback (x' ≫ s) s ⟶ pullback f s :=
    pullback.lift (pullback.fst (x' ≫ s) s ≫ p) (pullback.snd (x' ≫ s) s)
      (by rw [Category.assoc, hpf]; exact pullback.condition)
  have hc₁ : c ≫ pullback.fst f s = pullback.fst (x' ≫ s) s ≫ p := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd f s = pullback.snd (x' ≫ s) s := pullback.lift_snd _ _ _
  have big : IsPullback (pullback.fst (x' ≫ s) s) (c ≫ pullback.snd f s) (p ≫ f) s := by
    rw [hc₂, hpf]
    exact IsPullback.of_hasPullback (x' ≫ s) s
  have sq₁ : IsPullback (pullback.fst (x' ≫ s) s) c p (pullback.fst f s) :=
    big.of_bot hc₁.symm (IsPullback.of_hasPullback f s)
  have hQc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) c :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) sq₁ inferInstance,
      MorphismProperty.of_isPullback (P := @Flat) sq₁ inferInstance⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq₁ inferInstance⟩
  have key : ∀ {T : Scheme.{u}} (a : T ⟶ pullback (x' ≫ s) s) (b : T ⟶ X'),
      a ≫ c = b ≫ u → a ≫ A.act = b := by
    intro T a b h
    have h₁ : (a ≫ pullback.fst (x' ≫ s) s) ≫ p = b ≫ p := by
      rw [Category.assoc, ← hc₁, ← Category.assoc, h, Category.assoc, hu₁]
    have h₂ : a ≫ pullback.snd (x' ≫ s) s = b ≫ x' := by
      rw [← hc₂, ← Category.assoc, h, Category.assoc, hu₂]
    have hφ : hR.lift (a ≫ pullback.fst (x' ≫ s) s) b h₁ = a := by
      apply pullback.hom_ext
      · rw [hR.lift_fst]
      · rw [h₂, ← A.act_comp, ← Category.assoc, hR.lift_snd]
    rw [← hφ, hR.lift_snd]
  have comm : 𝟙 (pullback (x' ≫ s) s) ≫ c = A.act ≫ u := by
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [hc₁, Category.assoc, hu₁, w]
    · rw [hc₂, Category.assoc, hu₂, A.act_comp]
  have sq₂ : IsPullback (𝟙 (pullback (x' ≫ s) s)) A.act c u :=
    IsPullback.of_iso_pullback ⟨comm⟩
      { hom := pullback.lift (𝟙 _) A.act comm
        inv := pullback.fst c u
        hom_inv_id := pullback.lift_fst _ _ _
        inv_hom_id := by
          apply pullback.hom_ext
          · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
          · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
            exact key _ _ pullback.condition }
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hiso : (MorphismProperty.isomorphisms Scheme.{u}) u :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq₂ hQc
      ((MorphismProperty.isomorphisms.iff _).mpr inferInstance)
  have : IsIso u := (MorphismProperty.isomorphisms.iff _).mp hiso
  have hinv₁ : inv u ≫ p = pullback.fst f s := by rw [IsIso.inv_comp_eq, hu₁]
  have hinv₂ : inv u ≫ x' = pullback.snd f s := by rw [IsIso.inv_comp_eq, hu₂]
  have compat : ∀ m : pullback (pullback.snd f s ≫ s) s ⟶ pullback (x' ≫ s) s,
      m ≫ pullback.fst (x' ≫ s) s = pullback.fst _ _ ≫ inv u → m ≫ pullback.snd (x' ≫ s) s =
        pullback.snd _ _ →
      m ≫ A.act = DescentAction.flipMap s f ≫ inv u := by
    intro m hm₁ hm₂
    rw [IsIso.eq_comp_inv, Category.assoc]
    apply pullback.hom_ext
    · simp only [Category.assoc, hu₁]
      rw [← w, reassoc_of% hm₁, hinv₁, DescentAction.flipMap_fst]
    · simp only [Category.assoc, hu₂]
      rw [A.act_comp, hm₂, DescentAction.flipMap_snd]
  have he : (asIso u).symm.hom ≫ x' = pullback.snd f s := hinv₂
  refine ⟨(asIso u).symm, he, rfl, ?_⟩
  exact compat _ (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
end AlgebraicCurves.Geometry.Descent.Proofs.DescentAction_effective_of_isPullback_of_flat_surjective
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsSeparated_of_comp_of_universallyClosed_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Separatedness descends through a universally closed cover

If the first morphism is universally closed and surjective, separatedness of the
composite implies separatedness of the second morphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsSeparated_of_comp_of_universallyClosed_of_surjective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.IsSeparated.of_comp_of_universallyClosed_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated (f ≫ g)] [UniversallyClosed f]
    [Surjective f] : IsSeparated g := by
  have hsepBC : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => IsSeparated h) :=
    IsSeparated.isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) := by
    refine .mk' ?_
    introv hg
    simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
    rw [hg, Set.preimage_univ]
  have : MorphismProperty.IsStableUnderComposition
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) := by
    refine ⟨?_⟩
    intro X Y Z h k hh hk
    exact ⟨hk.surj.comp hh.surj⟩
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => UniversallyClosed h) :=
    universallyClosed_isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderComposition
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => UniversallyClosed h) :=
    universallyClosed_isStableUnderComposition
  let R : pullback f f ⟶ pullback (f ≫ g) (f ≫ g) :=
    pullback.map f f (f ≫ g) (f ≫ g) (𝟙 X) (𝟙 X) g (Category.id_comp _).symm
      (Category.id_comp _).symm
  let ff : pullback (f ≫ g) (f ≫ g) ⟶ pullback g g :=
    pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 _) (Category.comp_id _) (Category.comp_id _)
  have sq : IsPullback (pullback.fst f f ≫ f) R (pullback.diagonal g) ff :=
    pullback_map_diagonal_isPullback f f g
  have hR₁ : R ≫ pullback.fst (f ≫ g) (f ≫ g) = pullback.fst f f := by
    simp only [R, pullback.map, pullback.lift_fst, Category.comp_id]
  have : UniversallyClosed (R ≫ pullback.fst (f ≫ g) (f ≫ g)) := by rw [hR₁]; infer_instance
  have : IsSeparated (pullback.fst (f ≫ g) (f ≫ g)) :=
    hsepBC.of_isPullback (IsPullback.of_hasPullback (f ≫ g) (f ≫ g)).flip
      ‹IsSeparated (f ≫ g)›
  have : UniversallyClosed R := MorphismProperty.of_postcomp (W := @UniversallyClosed)
    (W' := @IsSeparated) R (pullback.fst (f ≫ g) (f ≫ g)) ‹_› ‹_›
  have hRcl : IsClosed (Set.range R) := by
    rw [← Set.image_univ]; exact R.isClosedMap _ isClosed_univ
  have hff₁ : Surjective ff :=
    MorphismProperty.pullbackMap (P := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h)
        ‹Surjective f› ‹Surjective f› rfl rfl
  have hff₂ : UniversallyClosed ff :=
    MorphismProperty.pullbackMap (P := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => UniversallyClosed
        h) ‹UniversallyClosed f›
      ‹UniversallyClosed f› rfl rfl
  have hsub : ff ⁻¹' Set.range (pullback.diagonal g) ⊆ Set.range R := by
    rintro w ⟨y, hy⟩
    obtain ⟨z, -, hz⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := pullback.diagonal g) (g := ff) y w hy
    exact ⟨sq.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, sq.isoPullback_inv_snd, hz]⟩
  have hrange : Set.range (pullback.diagonal g) = ff '' Set.range R := by
    apply subset_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨w, hw⟩ := hff₁.surj (pullback.diagonal g y)
      obtain ⟨r, hr⟩ := hsub ⟨y, hw.symm⟩
      exact ⟨R r, ⟨r, rfl⟩, by rw [hr, hw]⟩
    · rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
      refine ⟨(pullback.fst f f ≫ f) r, ?_⟩
      change ((pullback.fst f f ≫ f) ≫ pullback.diagonal g) r = (R ≫ ff) r
      rw [sq.w]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact ff.isClosedMap _ hRcl
  have : IsClosedImmersion (pullback.diagonal g) := .of_isPreimmersion _ hclosed
  exact ⟨‹_›⟩
end IsSeparated_of_comp_of_universallyClosed_of_surjective
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

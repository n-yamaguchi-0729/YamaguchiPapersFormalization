/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Normalization endomorphisms and smooth base change

An endomorphism of `X` over `S` extends to the relative normalization of
`f : X → S` by `normalizationDesc`.  The actual normalization/base-change
comparison commutes with this extension and the pulled-back endomorphism.
This compatibility follows from the uniqueness part of normalization and
holds for every base change.

For a smooth base change, including an etale chart, the comparison is an
isomorphism.  A point of the original normalization and a compatible lift of
its base point then determine a point of the base-changed normalization;
the two points have exactly the same fixing endomorphisms.  This applies to
geometric points and deck transformations without assuming the compatibility
of either action.  Localization of a stalk is not asserted to be smooth.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Pull back an actual endomorphism over the base, keeping the second factor
fixed.  The displayed equation is exactly the over-base condition. -/
def pullbackEndomorphism (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    pullback f g ⟶ pullback f g :=
  pullback.map f g f g σ (𝟙 Y) (𝟙 S)
    (by rw [Category.comp_id, hσ])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
theorem pullbackEndomorphism_fst (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    pullbackEndomorphism f g σ hσ ≫ pullback.fst f g =
      pullback.fst f g ≫ σ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem pullbackEndomorphism_snd (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    pullbackEndomorphism f g σ hσ ≫ pullback.snd f g = pullback.snd f g := by
  change pullback.lift _ _ _ ≫ pullback.snd f g = pullback.snd f g
  rw [pullback.lift_snd, Category.comp_id]

section Normalization

variable [QuasiCompact f] [QuasiSeparated f]

/-- Extend an endomorphism over the base by the universal property of relative
normalization.  This is the construction used for normalization deck maps. -/
def normalizationEndomorphism (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    f.normalization ⟶ f.normalization :=
  f.normalizationDesc (σ ≫ f.toNormalization) f.fromNormalization (by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hσ])

@[reassoc]
theorem toNormalization_normalizationEndomorphism
    (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    f.toNormalization ≫ normalizationEndomorphism f σ hσ =
      σ ≫ f.toNormalization :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

@[reassoc]
theorem normalizationEndomorphism_fromNormalization
    (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    normalizationEndomorphism f σ hσ ≫ f.fromNormalization = f.fromNormalization :=
  Scheme.Hom.normalizationDesc_comp _ _ _ _

/-- Normalization/base-change comparison intertwines the actual extended
endomorphisms.  Smoothness is unnecessary for this commuting square. -/
@[reassoc]
theorem normalizationPullback_endomorphism
    (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    normalizationEndomorphism (pullback.snd f g)
        (pullbackEndomorphism f g σ hσ)
        (pullbackEndomorphism_snd f g σ hσ) ≫
      f.normalizationPullback g =
    f.normalizationPullback g ≫
      pullbackEndomorphism f.fromNormalization g
        (normalizationEndomorphism f σ hσ)
        (normalizationEndomorphism_fromNormalization f σ hσ) := by
  refine Scheme.Hom.normalization.hom_ext (pullback.snd f g)
    _ _ (pullback.snd f.fromNormalization g) ?_ ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, toNormalization_normalizationEndomorphism_assoc,
        toNormalization_normalizationEndomorphism, pullbackEndomorphism_fst,
        pullbackEndomorphism_fst_assoc,
        Scheme.Hom.toNormalization_normalizationPullback_fst,
        Scheme.Hom.toNormalization_normalizationPullback_fst_assoc]
    · simp only [Category.assoc, pullbackEndomorphism_snd,
        Scheme.Hom.normalizationPullback_snd,
        normalizationEndomorphism_fromNormalization,
        Scheme.Hom.toNormalization_fromNormalization]
  · simp only [Category.assoc, Scheme.Hom.normalizationPullback_snd,
      normalizationEndomorphism_fromNormalization]
  · simp only [Category.assoc, pullbackEndomorphism_snd,
      Scheme.Hom.normalizationPullback_snd]

/-- Whenever the canonical comparison is an isomorphism, it conjugates the
two normalization endomorphisms. This applies to smooth base change and to
the canonical comparison constructed for an affine localization. -/
theorem normalizationPullback_conjugates_endomorphism [IsIso (f.normalizationPullback g)]
    (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    normalizationEndomorphism (pullback.snd f g)
        (pullbackEndomorphism f g σ hσ)
        (pullbackEndomorphism_snd f g σ hσ) =
      f.normalizationPullback g ≫
        pullbackEndomorphism f.fromNormalization g
          (normalizationEndomorphism f σ hσ)
          (normalizationEndomorphism_fromNormalization f σ hσ) ≫
        inv (f.normalizationPullback g) := by
  apply (cancel_mono (f.normalizationPullback g)).mp
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact normalizationPullback_endomorphism f g σ hσ

/-- When the canonical normalization comparison is an isomorphism, a point
and its compatible lift have exactly the same fixing endomorphisms.
For a geometric point, take `T = Spec Ω`.
The lifted point is constructed by the pullback universal property and the
inverse of the actual normalization comparison. -/
theorem normalizationPullback_fixes_point_iff [IsIso (f.normalizationPullback g)]
    {T : Scheme.{u}} (z : T ⟶ f.normalization) (y : T ⟶ Y)
    (hzy : z ≫ f.fromNormalization = y ≫ g)
    (σ : X ⟶ X) (hσ : σ ≫ f = f) :
    (pullback.lift z y hzy ≫ inv (f.normalizationPullback g)) ≫
        normalizationEndomorphism (pullback.snd f g)
          (pullbackEndomorphism f g σ hσ)
          (pullbackEndomorphism_snd f g σ hσ) =
      pullback.lift z y hzy ≫ inv (f.normalizationPullback g) ↔
    z ≫ normalizationEndomorphism f σ hσ = z := by
  rw [← cancel_mono (f.normalizationPullback g)]
  simp only [Category.assoc, normalizationPullback_endomorphism,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  constructor
  · intro h
    have hfst := congrArg
      (fun k ↦ k ≫ pullback.fst f.fromNormalization g) h
    simpa only [Category.assoc, pullbackEndomorphism_fst,
      pullback.lift_fst_assoc, pullback.lift_fst] using hfst
  · intro h
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackEndomorphism_fst,
        pullback.lift_fst_assoc, pullback.lift_fst, h]
    · simp only [Category.assoc, pullbackEndomorphism_snd, pullback.lift_snd]

end Normalization

end EtaleFundamentalGroups.Inertia

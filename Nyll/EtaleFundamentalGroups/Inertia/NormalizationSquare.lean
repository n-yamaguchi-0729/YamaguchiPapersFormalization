/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationBaseChange

/-!
# Relative normalization along an actual commuting square

A commuting square induces a map on relative normalizations, by applying the
universal property to the pullback of the target normalization. The map
preserves the base and commutes with compatible source endomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

variable {A B S T : Scheme.{u}}
  (f : A ⟶ S) (g : B ⟶ T) [QuasiCompact f] [QuasiSeparated f]
  [QuasiCompact g] [QuasiSeparated g]
  (a : A ⟶ B) (b : S ⟶ T) (h : a ≫ g = f ≫ b)

private def normalizationSquareLift :
    f.normalization ⟶ pullback g.fromNormalization b :=
  f.normalizationDesc
    (pullback.lift (a ≫ g.toNormalization) f (by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h]))
    (pullback.snd g.fromNormalization b) (by rw [pullback.lift_snd])

private theorem normalizationSquareLift_source :
    f.toNormalization ≫ normalizationSquareLift f g a b h =
      pullback.lift (a ≫ g.toNormalization) f (by
        rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h]) :=
  Scheme.Hom.toNormalization_normalizationDesc _ _ _ _

private theorem normalizationSquareLift_base :
    normalizationSquareLift f g a b h ≫ pullback.snd g.fromNormalization b =
      f.fromNormalization :=
  Scheme.Hom.normalizationDesc_comp _ _ _ _

/-- The normalization map induced by a displayed commuting square. -/
def normalizationMapOfSquare : f.normalization ⟶ g.normalization :=
  normalizationSquareLift f g a b h ≫ pullback.fst g.fromNormalization b

@[reassoc]
theorem normalizationMapOfSquare_source :
    f.toNormalization ≫ normalizationMapOfSquare f g a b h =
      a ≫ g.toNormalization := by
  rw [normalizationMapOfSquare, ← Category.assoc, normalizationSquareLift_source,
    pullback.lift_fst]

@[reassoc]
theorem normalizationMapOfSquare_base :
    normalizationMapOfSquare f g a b h ≫ g.fromNormalization =
      f.fromNormalization ≫ b := by
  rw [normalizationMapOfSquare, Category.assoc, pullback.condition,
    ← Category.assoc, normalizationSquareLift_base]

/-- The induced normalization map intertwines actual compatible source
endomorphisms. No comparison of the induced actions is assumed. -/
@[reassoc]
theorem normalizationMapOfSquare_endomorphism
    (τ : A ⟶ A) (hτ : τ ≫ f = f)
    (σ : B ⟶ B) (hσ : σ ≫ g = g)
    (he : τ ≫ a = a ≫ σ) :
    normalizationEndomorphism f τ hτ ≫ normalizationMapOfSquare f g a b h =
      normalizationMapOfSquare f g a b h ≫ normalizationEndomorphism g σ hσ := by
  let l : A ⟶ pullback g.fromNormalization b :=
    pullback.lift (a ≫ g.toNormalization) f (by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h])
  have hl : f.toNormalization ≫ normalizationSquareLift f g a b h = l :=
    normalizationSquareLift_source f g a b h
  have hlift :
      normalizationEndomorphism f τ hτ ≫ normalizationSquareLift f g a b h =
        normalizationSquareLift f g a b h ≫
          pullbackEndomorphism g.fromNormalization b
            (normalizationEndomorphism g σ hσ)
            (normalizationEndomorphism_fromNormalization g σ hσ) := by
    apply Scheme.Hom.normalization.hom_ext f _ _
      (pullback.snd g.fromNormalization b)
    · rw [← Category.assoc, toNormalization_normalizationEndomorphism,
        Category.assoc, hl, ← Category.assoc, hl]
      apply pullback.hom_ext
      · simp only [l, Category.assoc, pullback.lift_fst,
          pullbackEndomorphism_fst, pullback.lift_fst_assoc]
        rw [← Category.assoc, he, Category.assoc,
          toNormalization_normalizationEndomorphism]
      · simp only [l, Category.assoc, pullback.lift_snd,
          pullbackEndomorphism_snd, hτ]
    · rw [Category.assoc, normalizationSquareLift_base,
        normalizationEndomorphism_fromNormalization]
    · rw [Category.assoc, pullbackEndomorphism_snd, normalizationSquareLift_base]
  dsimp only [normalizationMapOfSquare]
  rw [← Category.assoc, hlift, Category.assoc, pullbackEndomorphism_fst,
    ← Category.assoc]

end EtaleFundamentalGroups.Inertia

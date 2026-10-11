/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationBaseChange
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Relative normalization under an isomorphism of source schemes

The comparison is constructed in both directions by normalizationDesc.
Its compatibility with endomorphisms follows from the same universal
property. It can therefore transport an actual cover to its affine spectrum
without replacing geometric-point equality by topological-point equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable {A B S : Scheme.{u}}
variable (f : A ⟶ S) (g : B ⟶ S)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
variable (e : A ≅ B) (he : e.hom ≫ g = f)

/-- An actual source isomorphism over the base extends to an isomorphism of
relative normalizations, by their universal properties. -/
def normalizationSourceIso : f.normalization ≅ g.normalization := by
  have hi : e.inv ≫ f = g := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine
    { hom := f.normalizationDesc (e.hom ≫ g.toNormalization) g.fromNormalization
        (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, he])
      inv := g.normalizationDesc (e.inv ≫ f.toNormalization) f.fromNormalization
        (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hi])
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · refine Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization ?_ ?_ ?_
    · simp only [Category.assoc, Scheme.Hom.toNormalization_normalizationDesc_assoc,
        Scheme.Hom.toNormalization_normalizationDesc, Iso.hom_inv_id_assoc,
        Category.comp_id]
    · simp only [Category.assoc, Scheme.Hom.normalizationDesc_comp]
    · exact Category.id_comp _
  · refine Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization ?_ ?_ ?_
    · simp only [Category.assoc, Scheme.Hom.toNormalization_normalizationDesc_assoc,
        Scheme.Hom.toNormalization_normalizationDesc, Iso.inv_hom_id_assoc,
        Category.comp_id]
    · simp only [Category.assoc, Scheme.Hom.normalizationDesc_comp]
    · exact Category.id_comp _

@[reassoc]
theorem toNormalization_normalizationSourceIso_hom :
    f.toNormalization ≫ (normalizationSourceIso f g e he).hom =
      e.hom ≫ g.toNormalization :=
  Scheme.Hom.toNormalization_normalizationDesc f (e.hom ≫ g.toNormalization)
    g.fromNormalization (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, he])

@[reassoc]
theorem normalizationSourceIso_hom_fromNormalization :
    (normalizationSourceIso f g e he).hom ≫ g.fromNormalization = f.fromNormalization :=
  Scheme.Hom.normalizationDesc_comp f (e.hom ≫ g.toNormalization)
    g.fromNormalization (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, he])

/-- Extending commuting endomorphisms preserves their commutation with the
actual source isomorphism. -/
@[reassoc]
theorem normalizationSourceIso_hom_endomorphism
    (sigma : A ⟶ A) (hsigma : sigma ≫ f = f)
    (tau : B ⟶ B) (htau : tau ≫ g = g)
    (hcommute : sigma ≫ e.hom = e.hom ≫ tau) :
    normalizationEndomorphism f sigma hsigma ≫ (normalizationSourceIso f g e he).hom =
      (normalizationSourceIso f g e he).hom ≫ normalizationEndomorphism g tau htau := by
  refine Scheme.Hom.normalization.hom_ext f _ _ g.fromNormalization ?_ ?_ ?_
  · simp only [toNormalization_normalizationEndomorphism_assoc,
      toNormalization_normalizationSourceIso_hom_assoc,
      toNormalization_normalizationSourceIso_hom,
      toNormalization_normalizationEndomorphism]
    rw [← Category.assoc, hcommute, Category.assoc]
  · simp only [Category.assoc, normalizationSourceIso_hom_fromNormalization,
      normalizationEndomorphism_fromNormalization]
  · simp only [Category.assoc, normalizationSourceIso_hom_fromNormalization,
      normalizationEndomorphism_fromNormalization]

/-- The resulting comparison preserves exact fixed geometric-point morphisms. -/
theorem normalizationSourceIso_fixes_iff
    {T : Scheme.{u}} (z : T ⟶ f.normalization)
    (sigma : A ⟶ A) (hsigma : sigma ≫ f = f)
    (tau : B ⟶ B) (htau : tau ≫ g = g)
    (hcommute : sigma ≫ e.hom = e.hom ≫ tau) :
    (z ≫ (normalizationSourceIso f g e he).hom) ≫ normalizationEndomorphism g tau htau =
        z ≫ (normalizationSourceIso f g e he).hom ↔
      z ≫ normalizationEndomorphism f sigma hsigma = z := by
  rw [← cancel_mono (normalizationSourceIso f g e he).hom]
  simp only [Category.assoc, normalizationSourceIso_hom_endomorphism f g e he
    sigma hsigma tau htau hcommute]

end EtaleFundamentalGroups.Inertia

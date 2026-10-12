/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperLocalFiniteEtaleSections
import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperNoetherianConnectedFibers
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.Morphisms.ProperNormalization
import Nyll.SchemeTheory.Morphisms.EtalePostcomposition
import Mathlib.RingTheory.RingHom.Finite

/-!
# The Stein factor over an arbitrary local base

The actual section algebra computed by Noetherian approximation identifies
the second map of relative normalization as finite étale. Its first map has
geometrically connected fibres by the unrestricted scalar-section comparison.
The original local base is not assumed Noetherian.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The second native normalization map of a proper flat finitely presented
geometrically reduced family over an arbitrary local ring is finite étale. -/
theorem finite_etale_fromNormalization_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    IsFiniteEtale f.fromNormalization := by
  let hRΓ : Algebra R Γ(X, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
  obtain ⟨hFinite, _, hEtale⟩ :=
    finite_projective_etale_sectionAlgebra_of_proper_flat_geometricallyReduced_local f
  have hApp : f.appTop = f.appLE ⊤ ⊤ le_top := f.app_eq_appLE
  have hScalar : algebraMap R Γ(X, ⊤) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom := by
    change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      f.appLE ⊤ ⊤ le_top).hom) = _
    rw [← hApp]
  have hFiniteApp : f.appTop.hom.Finite := by
    apply (RingHom.finite_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv f.appTop).mp
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.Finite
    rw [← hScalar]
    exact hFinite
  have hEtaleApp : f.appTop.hom.Etale := by
    apply (RingHom.Etale.respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv f.appTop).mp
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.Etale
    rw [← hScalar]
    exact hEtale
  have hFactor : f.fromNormalization.appTop ≫ f.toNormalization.appTop = f.appTop := by
    rw [← Scheme.Hom.comp_appTop, f.toNormalization_fromNormalization]
  have hFiniteNorm : f.fromNormalization.appTop.hom.Finite := by
    apply (RingHom.finite_respectsIso.cancel_right_isIso
      f.fromNormalization.appTop f.toNormalization.appTop).mp
    change (f.fromNormalization.appTop ≫ f.toNormalization.appTop).hom.Finite
    rw [hFactor]
    exact hFiniteApp
  have hEtaleNorm : f.fromNormalization.appTop.hom.Etale := by
    apply (RingHom.Etale.respectsIso.cancel_right_isIso
      f.fromNormalization.appTop f.toNormalization.appTop).mp
    change (f.fromNormalization.appTop ≫ f.toNormalization.appTop).hom.Etale
    rw [hFactor]
    exact hEtaleApp
  exact (HasAffineProperty.iff_of_isAffine
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    (Q := affineAnd RingHom.FiniteEtale) (f := f.fromNormalization)).mpr
    ⟨inferInstance, (RingHom.FiniteEtale.iff_finite_and_etale _).mpr
      ⟨hEtaleNorm, hFiniteNorm⟩⟩

/-- The first native normalization map has geometrically connected fibres
for the same family over an arbitrary local ring. -/
theorem geometricallyConnected_toNormalization_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    GeometricallyConnected f.toNormalization := by
  have hFiniteEtale : IsFiniteEtale f.fromNormalization :=
    finite_etale_fromNormalization_of_proper_flat_geometricallyReduced_local f
  have hFlat : Flat (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸ (inferInstance : Flat f)
  have hPresentation : LocallyOfFinitePresentation
      (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸
      (inferInstance : LocallyOfFinitePresentation f)
  have hReduced : GeometricallyReduced (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸ (inferInstance : GeometricallyReduced f)
  obtain ⟨hFirstFlat, hFirstPresentation, hFirstReduced⟩ :=
    flat_finitePresentation_geometricallyReduced_of_comp_etale
      f.toNormalization f.fromNormalization
  have hSections : IsIso f.toNormalization.c := f.isIso_toNormalization_c
  exact geometricallyConnected_of_proper_flat_geometricallyReduced_of_isIso_c
    f.toNormalization

end AlgebraicGeometry

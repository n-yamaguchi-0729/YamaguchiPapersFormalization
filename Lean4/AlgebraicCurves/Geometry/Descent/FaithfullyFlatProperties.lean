/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

Copyright (c) 2026 Naganori Yamaguchi.
Authors of the faithfully flat generalization: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import AlgebraicCurves.Geometry.Schemes.Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact
import AlgebraicCurves.Geometry.Curves.smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange

/-!
# Geometric properties descend along a faithfully flat affine base change

Flatness, surjectivity and quasi-compactness are the only hypotheses used.
In particular inseparable finite extensions of fields are covered.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicCurves.Geometry.Curves.Proofs
open smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange.AlgebraicGeometry
open FiniteEtaleBaseChangeDescent

namespace AlgebraicGeometry

/-- Smoothness, properness and geometric connectedness descend along any faithfully
flat change of affine base. -/
theorem smooth_isProper_geometricallyConnected_of_faithfullyFlat_baseChange
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) {X' : Scheme.{u}} (x' : X' ⟶ Spec
      (CommRingCat.of R'))
    (hsm : Smooth x') (hpr : IsProper x') (hgc : GeometricallyConnected x')
    (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X')
    (he : e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Smooth f ∧ IsProper f ∧ GeometricallyConnected f := by
  have hff : (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hfl, hsu⟩ := (flat_and_surjective_SpecMap_iff _).mpr hff
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map
    (CommRingCat.ofHom (algebraMap R R'))) :=
    ⟨⟨hsu, hfl⟩, inferInstance⟩
  have hres (P : MorphismProperty Scheme.{u}) (hbc : P.IsStableUnderBaseChange) : P.RespectsIso :=
    by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    hres (@Smooth : MorphismProperty Scheme.{u}) smooth_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    hres (@IsProper : MorphismProperty Scheme.{u}) IsProper.isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    hres (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (GeometricallyConnected.eq_geometrically ▸ inferInstance)
  have hsm' : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]; exact (MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom x').mpr hsm
  have hpr' : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]; exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom x').mpr hpr
  have hgc' : GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R
    R')))) := by
    rw [← he]; exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom
      x').mpr hgc
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := hsu
  refine ⟨?_, ?_, ?_⟩
  · have := AlgebraicGeometry.Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hσ hsm'
  · have := isProper_descendsAlong.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsProper)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hσ hpr'
  · exact geometricallyConnected_of_pullback_snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))

end AlgebraicGeometry

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

The finite faithfully-flat theorem is a specialization of the affine, flat,
and surjective rigidified-isomorphism theorem. Its public statement and
upstream notice are retained above and below.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections

/-!
# Faithfully flat reflection of rigidified line bundle isomorphisms

Apply affine descent to the finite faithfully flat base change.
-/

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

theorem nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
          (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L ≅
      (M₂.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by
  have hFinite : IsFinite (specMap R R') :=
    (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr
      (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite R R'))
  have hSpec : Flat (specMap R R') ∧ Surjective (specMap R R') :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstance : Module.FaithfullyFlat R R'))
  let π : SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t :=
    ⟨pullback.fst t (specMap R R'), pullback.condition⟩
  have : IsAffineHom π.1 :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback t (specMap R R')).flip
      (IsFinite.toIsAffineHom (f := specMap R R'))
  have : Flat π.1 :=
    MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback t (specMap R R')).flip hSpec.1
  have : Surjective π.1 :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback t (specMap R R')).flip hSpec.2
  exact nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
    R c ε hH0 t (pullback.snd t (specMap R R') ≫ specMap R R') π M₁ M₂ h

end AlgebraicGeometry.RelPicard.RigidifiedLineBundle

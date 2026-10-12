/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
# Relative Picard varieties and fibre cohomology

Restrict a representing relative Picard designation along a base change.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite

namespace AlgebraicGeometry.RelPicard.BaseChange

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

/-- Restrict the base-changed representing designation through the canonical relative sub-
Picard presheaf isomorphism. -/
noncomputable def representableByRestrict {D' : RelativePic0Designation R' (baseChange R c R')}
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) D') :
    ((Over.map (specMap R R')).op ⋙ relSubPicPresheaf c ε (algEquivZeroCut c ε)).RepresentableBy
      (Over.mk D'.toBase) :=
  h'.representableBy.ofIso (relSubPicPresheafAlgEquivZeroCutIso c ε R')

end AlgebraicGeometry.RelPicard.BaseChange

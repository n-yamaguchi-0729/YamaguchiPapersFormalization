/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativePic0DesignationBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.Picard.Designation
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
Base change of a relative Picard-zero designation and the resulting structure morphism and zero
section.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

namespace GoodReductionJacobian.RelativePic0Designation

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

/-- Base change of the designated Picard-zero scheme together with its zero section. -/
abbrev baseChange (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R'] :
    RelativePic0Designation R' (SmoothProperCurve.baseChange R c R') where
  P := pullback D.toBase (specMap R R')
  toBase := pullback.snd D.toBase (specMap R R')
  zeroSection := pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
    (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp])
  zeroSection_toBase := pullback.lift_snd _ _ _

variable (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']

theorem baseChange_P : (D.baseChange R').P = pullback D.toBase (specMap R R') := rfl

theorem baseChange_toBase : (D.baseChange R').toBase = pullback.snd D.toBase (specMap R R') := rfl

theorem baseChange_zeroSection :
    (D.baseChange R').zeroSection = pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
      (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp]) := rfl

theorem baseChange_zeroSection_fst :
    (D.baseChange R').zeroSection ≫ pullback.fst D.toBase (specMap R R') = specMap R R' ≫
      D.zeroSection :=
  pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativePic0Designation

end

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawAction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw

/-!
# Action
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

/-- The structure morphism of the source of the restricted group action. -/
abbrev actionSource (f : J ⟶ Spec (CommRingCat.of R)) {E : Scheme.{u}} (ι : E ⟶ J) :
    pullback (ι ≫ f) f ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (ι ≫ f) f ≫ f

/-- The point given by the first projection followed by the inclusion into the group scheme. -/
def actionFstPoint (_L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    SchemeHomOver (actionSource f ι) f :=
  ⟨pullback.fst (ι ≫ f) f ≫ ι, by rw [Category.assoc, pullback.condition]⟩

/-- The point given by the second projection of the action source. -/
def actionSndPoint (_L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    SchemeHomOver (actionSource f ι) f :=
  ⟨pullback.snd (ι ≫ f) f, rfl⟩

/-- The action obtained by multiplying the included point by the second group coordinate. -/
def action (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) : pullback (ι ≫ f) f ⟶ J :=
  (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).1

theorem action_def (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    L.action ι = (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).1 := rfl

@[simp] theorem actionFstPoint_coe (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    (L.actionFstPoint ι).1 = pullback.fst (ι ≫ f) f ≫ ι := rfl

@[simp] theorem actionSndPoint_coe (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    (L.actionSndPoint ι).1 = pullback.snd (ι ≫ f) f := rfl

theorem action_over (L : RelativeGroupLaw R f) {E : Scheme.{u}} (ι : E ⟶ J) :
    L.action ι ≫ f = actionSource f ι :=
  (L.mul (actionSource f ι) (L.actionFstPoint ι) (L.actionSndPoint ι)).2

end GoodReductionJacobian.RelativeGroupLaw

end

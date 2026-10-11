/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardThetaBundle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule

/-!
# Twists by a rigidifying section

Defines the ideal and module twists of the rigidifying section after base change.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec
    (CommRingCat.of R))

/-- The ideal sheaf of the rigidifying section after base change. -/
def sectionIdeal : (pullback c t).IdealSheafData := (rigSection c t ε).ker

/-- The inverse ideal module of the rigidifying section raised to the given power. -/
def sectionTwist (r : ℕ) : (pullback c t).Modules := ((sectionIdeal c ε t) ^ r).invModule

/-- The pullback of a module to the fibre over the given field-valued point. -/
abbrev fibreModule {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (F : (pullback c t).Modules) : (pullback (pullback.snd c t) s).Modules :=
  (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj F

end AlgebraicGeometry.RelPicard

end

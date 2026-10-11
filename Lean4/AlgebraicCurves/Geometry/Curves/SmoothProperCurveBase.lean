/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SmoothProperCurveBase.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
Scalar extensions of smooth proper curves, their sections and their basic fibre properties.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry

instance SmoothOfRelativeDimension.smooth_one {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

instance SmoothOfRelativeDimension.pullback_snd (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (pullback.snd f g) :=
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => SmoothOfRelativeDimension n h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  hbc.of_isPullback (IsPullback.of_hasPullback f g) ‹SmoothOfRelativeDimension n f›

instance SmoothOfRelativeDimension.pullback_fst (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (pullback.fst f g) :=
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => SmoothOfRelativeDimension n h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  hbc.of_isPullback (IsPullback.of_hasPullback f g).flip ‹SmoothOfRelativeDimension n g›

instance SmoothOfRelativeDimension.fiberToSpecResidueField (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (s : S) :
    SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) :=
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => SmoothOfRelativeDimension n h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  hbc.of_isPullback (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
    ‹SmoothOfRelativeDimension n f›

instance IsProper.fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S) :
    IsProper (f.fiberToSpecResidueField s) :=
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => IsProper h) :=
    IsProper.isStableUnderBaseChange
  hbc.of_isPullback (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) ‹IsProper f›

namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

/-- The spectrum map induced by the scalar extension. -/
abbrev specMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R T))

/-- The pullback curve along the spectrum map of a scalar extension. -/
abbrev baseChange : pullback c (specMap R T) ⟶ Spec (CommRingCat.of T) :=
  pullback.snd c (specMap R T)

example [SmoothOfRelativeDimension 1 c] : SmoothOfRelativeDimension 1 (baseChange R c T) :=
  inferInstance
example [IsProper c] : IsProper (baseChange R c T) := inferInstance
example [GeometricallyIntegral c] : GeometricallyIntegral (baseChange R c T) := inferInstance

variable {R c}

/-- The section of the scalar-extension pullback induced by the original section. -/
def sectionBaseChange (ε : SchemeHomOver (𝟙 _) c) : SchemeHomOver (𝟙 _) (baseChange R c T) :=
  ⟨pullback.lift (specMap R T ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2]; simp),
    pullback.lift_snd _ _ _⟩
@[simp]
theorem sectionBaseChange_coe_fst (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.fst c (specMap R T) = specMap R T ≫ ε.1 :=
  pullback.lift_fst _ _ _
@[simp]
theorem sectionBaseChange_coe_snd (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.snd c (specMap R T) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end BaseChange

instance isIntegral_pullback_Spec_field [GeometricallyIntegral c] {K : Type u} [Field K]
    (ξ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) : IsIntegral (pullback c ξ) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c ξ)

example [GeometricallyIntegral c] (K : Type u) [Field K] [Algebra R K] :
    IsIntegral (pullback c (specMap R K)) := inferInstance

end SmoothProperCurve

end AlgebraicGeometry

end

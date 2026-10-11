/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed
import SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent

/-!
# geometrically Integral of forall is Alg Closed is Integral pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType
      f]
    (hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec
      (CommRingCat.of R)),
      AlgebraicGeometry.IsIntegral (pullback f s)) :
    GeometricallyIntegral f := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro K _ y Z fst snd hZ
  suffices hI : AlgebraicGeometry.IsIntegral (pullback f y) by
    have := hI
    exact AlgebraicGeometry.IsIntegral.of_isIso hZ.isoPullback.inv
  let Kb := AlgebraicClosure K
  let t : Spec (CommRingCat.of Kb) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom
    (algebraMap K Kb))
  have : AlgebraicGeometry.IsIntegral (pullback (pullback.snd f y) t) := by
    have hP := (IsPullback.of_hasPullback (pullback.snd f y) t).paste_horiz
      (IsPullback.of_hasPullback f y)
    have := hgeo Kb (t ≫ y)
    exact AlgebraicGeometry.IsIntegral.of_isIso hP.isoPullback.inv
  have : GeometricallyIntegral (pullback.snd (pullback.snd f y) t) :=
    geometricallyIntegral_of_isAlgClosed _
  have : GeometricallyIntegral (pullback.snd f y) :=
    GeometricallyIntegral.of_isPullback_of_geometricallyIntegral (pullback.snd f y)
      (pullback.snd (pullback.snd f y) t) (pullback.fst (pullback.snd f y) t)
        (IsPullback.of_hasPullback _ _)
  exact self_of_isIntegral_of_geometrically (f := pullback.snd f y)
    GeometricallyIntegral.geometrically_isIntegral
end geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation

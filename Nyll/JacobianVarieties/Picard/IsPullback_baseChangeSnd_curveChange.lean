/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd_curveChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.SchemeTheory.CategoryTheory.Pullback

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback

/-!
# The pullback square for a change of curve
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsPullback_baseChangeSnd_curveChange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.RelPicard

theorem _root_.AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd_curveChange
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c')
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c' ψ) (curveChange f hf t')
      (curveChange f hf t) (baseChangeSnd c ψ) := by
  have sq : IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) :=
    CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq c c' t f hf
  have sq' : IsPullback (pullback.fst c' t') (curveChange f hf t') f (pullback.fst c t') :=
    CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq c c' t' f hf
  have e₁ : baseChangeSnd c' ψ ≫ pullback.fst c' t = pullback.fst c' t' :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have e₂ : baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [← e₁, ← e₂] at sq'
  exact IsPullback.of_right sq' (curveChange_baseChangeSnd f hf ψ).symm sq
end JacobianVarieties.Picard.Proofs.IsPullback_baseChangeSnd_curveChange
end ProofImplementation

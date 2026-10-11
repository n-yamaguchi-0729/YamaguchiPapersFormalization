/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati

/-!
# is Pullback lift fst comp fst snd comp fst prod Str
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation


theorem _root_.AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
    {S R : Type} [CommRing S] [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ←
          Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by
  have hg : IsPullback (pullback.fst f σ) (pullback.snd f σ) f σ := IsPullback.of_hasPullback f σ
  have s₁ : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ)) (pullback.fst
    (pullback.snd f σ) (pullback.snd f σ))
      (pullback.snd f σ) (pullback.snd f σ) := (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rw [hg.w]
    exact s₁.paste_horiz hg
  have s' : IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ←
          Category.assoc, pullback.condition,
          Category.assoc]) ≫ pullback.snd f f)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rwa [pullback.lift_snd]
  have step1 := IsPullback.of_right s' (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f
    f).flip
  exact step1.paste_vert hg
end AlgebraicCurves.Geometry.Schemes.Proofs.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
end ProofImplementation

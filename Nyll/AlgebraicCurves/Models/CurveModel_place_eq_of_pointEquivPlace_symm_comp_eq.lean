/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic

/-!
# Curve Model place eq of point Equiv Place symm comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem _root_.AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (𝔐 : AlgebraicCurve.CurveModel K L)
    {X B : Scheme.{u}} (πX : X ⟶ B) (s : Spec (CommRingCat.of K) ⟶ B)
    (e : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX s) (he : IsIso e)
    (he_snd : e ≫ CategoryTheory.Limits.pullback.snd πX s = 𝔐.toBase)
    (P Q : Place K L)
    (h : (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s =
      (𝔐.pointEquivPlace.symm Q).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s) :
    P = Q := by
  have h2 : (𝔐.pointEquivPlace.symm P).1 ≫ e = (𝔐.pointEquivPlace.symm Q).1 ≫ e := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · simpa only [Category.assoc] using h
    · rw [Category.assoc, he_snd, (𝔐.pointEquivPlace.symm P).2, Category.assoc, he_snd,
        (𝔐.pointEquivPlace.symm Q).2]
  have := he
  have h3 : (𝔐.pointEquivPlace.symm P).1 = (𝔐.pointEquivPlace.symm Q).1 := (cancel_mono e).mp h2
  exact 𝔐.pointEquivPlace.symm.injective (Subtype.ext h3)
end AlgebraicCurves.Models.Proofs.CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq
end ProofImplementation

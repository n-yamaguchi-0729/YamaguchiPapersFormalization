/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_isRational_pointEquivPlace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Place_isRational_of_range_stalk_section_eq
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Places.Evaluation

/-!
# Curve Model is Rational point Equiv Place
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_isRational_pointEquivPlace

open CategoryTheory AlgebraicGeometry

universe u v

theorem _root_.AlgebraicCurve.CurveModel.isRational_pointEquivPlace
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L)
    (x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    (M.pointEquivPlace x).IsRational := by
  classical
  let := M.functionFieldAlgebra
  have hff : ∀ a : K, M.ffEquiv (algebraMap K L a) = algebraMap K M.C.functionField a :=
    M.ffEquiv_algebraMap
  have hrat' : (AlgebraicCurve.Place.congrRingEquiv M.ffEquiv hff (M.pointEquivPlace x)).IsRational
    := by
    refine AlgebraicCurve.Place.isRational_of_range_stalk_section_eq M.toBase x.1 x.2
      (AlgebraicCurve.Place.congrRingEquiv M.ffEquiv hff (M.pointEquivPlace x)) ?_
    rw [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring]
    have h := M.range_stalk_eq (pointEquivClosedPoint M.toBase x)
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      change M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.pointEquivPlace x).toValuationSubring
      have : M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.placeOfPoint (pointEquivClosedPoint M.toBase
        x)).toValuationSubring.toSubring :=
        h ▸ ⟨s, rfl⟩
      exact this
    · intro hg
      have hg' : M.ffEquiv.symm g ∈ (M.placeOfPoint (pointEquivClosedPoint M.toBase
        x)).toValuationSubring.toSubring := hg
      rw [← h] at hg'
      obtain ⟨s, hs⟩ := hg'
      refine ⟨s, M.ffEquiv.symm.injective ?_⟩
      exact hs
  intro r
  obtain ⟨a, ha⟩ := hrat' (AlgebraicCurve.Place.congrResidueAlgEquiv M.ffEquiv hff
    (M.pointEquivPlace x) r)
  refine ⟨a, (AlgebraicCurve.Place.congrResidueAlgEquiv M.ffEquiv hff (M.pointEquivPlace
    x)).injective ?_⟩
  rw [AlgEquiv.commutes]
  exact ha
end AlgebraicCurves.Models.Proofs.CurveModel_isRational_pointEquivPlace
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

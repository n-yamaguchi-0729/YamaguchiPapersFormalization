/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_IsCurveOver_trdeg_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.FunctionFields.IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Mathlib.RingTheory.Unramified.Field

/-!
# Is Curve Over trdeg eq one
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.IsCurveOver_trdeg_eq_one

open AlgebraicCurve IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem _root_.AlgebraicCurve.IsCurveOver.trdeg_eq_one
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    Algebra.trdeg K F = 1 := by
  have hex : ∃ x : F, Transcendental K x := by
    by_contra h
    push Not at h
    have : Algebra.IsAlgebraic K F := ⟨fun x => not_not.1 (h x)⟩
    have : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
    exact false_of_nontrivial_of_subsingleton Ω[F⁄K]
  obtain ⟨x, hx⟩ := hex
  have hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hx
  apply le_antisymm
  · have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
      Algebra.IsAlgebraic.of_finite _ F
    have : Algebra.IsAlgebraic (Algebra.adjoin K ({x} : Set F)) F :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Algebra.adjoin K ({x} : Set F))
        (K := IntermediateField.adjoin K ({x} : Set F)) (C := F)).2 inferInstance
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x} : Set F)
    rwa [Cardinal.mk_singleton] at h
  · have hind : AlgebraicIndependent K ![x] := algebraicIndependent_iff_transcendental.2 hx
    have h := hind.lift_cardinalMk_le_trdeg
    rw [Cardinal.mk_fintype, Fintype.card_unique] at h
    simpa using h
end AlgebraicCurves.FunctionFields.Proofs.IsCurveOver_trdeg_eq_one
end ProofImplementation

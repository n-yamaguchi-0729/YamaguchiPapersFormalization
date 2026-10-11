/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_card_fiberAlong_le_finrankAlong_and_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Geometry.FundamentalIdentityAlong
import AlgebraicCurves.Places.Place_one_le_ramificationIndexAlong

/-!
# Place card fiber Along le finrank Along and iff
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_card_fiberAlong_le_finrankAlong_and_iff
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff
    {K F F' : Type*} [Field K] [IsAlgClosed K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong
      K φ)
    (P : Place K F) :
    (Place.fiberAlong φ hφ P).card ≤ finrankAlong K φ ∧
      ((Place.fiberAlong φ hφ P).card = finrankAlong K φ ↔
        ∀ W ∈ Place.fiberAlong φ hφ P, W.ramificationIndexAlong φ = 1) := by
  have hFI := AlgebraicCurve.fundamentalIdentityAlong φ hφ hfin hsep
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : FundamentalIdentity K F F' := hFI
  have key := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := K) (F := F) (F' := F') P
  simp only [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at key
  have hsum : ∑ w ∈ Place.fiberAlong φ hφ P, w.ramificationIndexAlong φ = finrankAlong K φ := by
    change ∑ w ∈ P.fiber F', w.ramificationIndex F = Module.finrank F F'
    exact_mod_cast key
  have hone : ∀ w ∈ Place.fiberAlong φ hφ P, 1 ≤ w.ramificationIndexAlong φ :=
    fun w _ => AlgebraicCurve.Place.one_le_ramificationIndexAlong φ hφ w
  have hcard : (Place.fiberAlong φ hφ P).card = ∑ w ∈ Place.fiberAlong φ hφ P, 1 := by
    rw [Finset.card_eq_sum_ones]
  refine ⟨?_, ?_⟩
  · rw [hcard, ← hsum]; exact Finset.sum_le_sum hone
  · rw [hcard, ← hsum, Finset.sum_eq_sum_iff_of_le hone]
    exact ⟨fun h w hw => (h w hw).symm, fun h w hw => (h w hw).symm⟩
end AlgebraicCurves.Places.Proofs.Place_card_fiberAlong_le_finrankAlong_and_iff
end ProofImplementation

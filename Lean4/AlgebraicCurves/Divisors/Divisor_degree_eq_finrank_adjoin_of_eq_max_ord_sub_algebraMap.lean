/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord

/-!
# Divisor degree eq finrank adjoin of eq max ord sub algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve

namespace FibreDegE96

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adicValuation_eq_exp (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem ord_sub_algebraMap_of_neg (v : Place K F) {x : F} (hx : x ≠ 0) (a : K) (hxa : x -
  algebraMap K F a ≠ 0)
    (h : v.ord x < 0) : v.ord (x - algebraMap K F a) = v.ord x := by
  have hc : v.adicValuation (algebraMap K F a) ≤ 1 := v.adicValuation_algebraMap_le_one a
  have hxv : 1 < v.adicValuation x := by
    rw [adicValuation_eq_exp v hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hlt : v.adicValuation (-algebraMap K F a) < v.adicValuation x := by
    rw [Valuation.map_neg]; exact lt_of_le_of_lt hc hxv
  have heq : v.adicValuation (x - algebraMap K F a) = v.adicValuation x := by
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ hlt]
  rw [adicValuation_eq_exp v hxa, adicValuation_eq_exp v hx] at heq
  have := WithZero.exp_injective heq
  omega

theorem ord_sub_algebraMap_nonneg (v : Place K F) {x : F} (hx : x ≠ 0) (a : K) (hxa : x -
  algebraMap K F a ≠ 0)
    (h : 0 ≤ v.ord x) : 0 ≤ v.ord (x - algebraMap K F a) := by
  have hc : v.adicValuation (algebraMap K F a) ≤ 1 := v.adicValuation_algebraMap_le_one a
  have hxv : v.adicValuation x ≤ 1 := by
    rw [adicValuation_eq_exp v hx, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hle : v.adicValuation (x - algebraMap K F a) ≤ 1 :=
    (Valuation.map_sub _ _ _).trans (max_le hxv hc)
  rw [adicValuation_eq_exp v hxa, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  omega

end FibreDegE96

theorem _root_.AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (a : K) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a))) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
  classical
  have hxa : x - algebraMap K F a ≠ 0 := by
    intro h
    apply hx
    rw [sub_eq_zero] at h
    rw [h]
    exact isAlgebraic_algebraMap a
  have hx0 : x ≠ 0 := by
    intro h; apply hx; rw [h]; exact isAlgebraic_zero
  obtain ⟨P, hP, hP0⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor _ hxa
  let Dinf : Divisor K F := P.mapRange (fun n => max 0 (-n)) (by simp)
  have hDinf : ∀ v : Place K F, Dinf v = max 0 (-v.ord x) := by
    intro v
    change max 0 (-P v) = _
    rw [hP v]
    rcases lt_or_ge (v.ord x) 0 with h | h
    · rw [FibreDegE96.ord_sub_algebraMap_of_neg v hx0 a hxa h]
    · have h' := FibreDegE96.ord_sub_algebraMap_nonneg v hx0 a hxa h
      rw [max_eq_left
        (by omega : -v.ord (x - algebraMap K F a) ≤ 0), max_eq_left (by omega : -v.ord x ≤ 0)]
  have hsplit : D - Dinf = P := by
    ext v
    rw [Finsupp.sub_apply, hD v]
    change max 0 (v.ord (x - algebraMap K F a)) - max 0 (-P v) = P v
    rw [hP v]
    omega
  have hdeg : Divisor.degree D = Divisor.degree Dinf := by
    have := congrArg Divisor.degree hsplit
    rw [map_sub, hP0] at this
    omega
  rw [hdeg]
  exact AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx Dinf hDinf
end AlgebraicCurves.Divisors.Proofs.Divisor_degree_eq_finrank_adjoin_of_eq_max_ord_sub_algebraMap
end ProofImplementation

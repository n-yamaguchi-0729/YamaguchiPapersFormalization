/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Place_ordDiff_eq_ordDifferential_of_perfectField
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver

/-!
# Regular Diffs eq regular Differentials of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.RegularDiffs_eq_regularDifferentials_of_perfectField
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open AlgebraicCurve

namespace S33PF

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_ord_nonneg (w : Place K F) {x : F} (hx : x ≠ 0) :
    x ∈ w.toValuationSubring ↔ 0 ≤ w.ord x := by
  rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
    WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx), WithZero.exp_zero]

theorem mem_of_ord_nonneg (w : Place K F) {x : F} (h : 0 ≤ w.ord x) : x ∈ w.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  · exact (mem_iff_ord_nonneg w hx).mpr h

theorem ord_nonneg_of_mem (w : Place K F) {x : F} (h : x ∈ w.toValuationSubring) : 0 ≤ w.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Place.ord_zero]
  · exact (mem_iff_ord_nonneg w hx).mp h

theorem regularDiffs_eq [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    regularDiffs K F = regularDifferentials K F := by
  have hgen : ∀ v : Place K F, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have key : ∀ (ω : Ω[F⁄K]) (v : Place K F),
      0 ≤ v.ordDiff ω ↔ ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord := by
    intro ω v
    rw [AlgebraicCurve.Place.ordDiff_eq_ordDifferential_of_perfectField v ω]
    constructor
    · intro h
      exact ⟨v.differentialCoeff ω, mem_of_ord_nonneg v h, (v.differentialCoeff_smul_dCoord ω).symm⟩
    · rintro ⟨f, hf, rfl⟩
      change 0 ≤ v.ord (v.differentialCoeff (f • v.dCoord))
      rw [v.differentialCoeff_unique (rfl : f • v.dCoord = f • v.dCoord)]
      exact ord_nonneg_of_mem v hf
  apply le_antisymm
  · rw [regularDiffs_eq_span]
    refine Submodule.span_le.mpr (fun ω hω => ?_)
    rw [SetLike.mem_coe, mem_regularDifferentials_iff]
    exact fun v => (key ω v).mp (hω v)
  · intro ω hω
    rw [mem_regularDifferentials_iff] at hω
    exact mem_regularDiffs_of_isRegularDiff (fun v => (key ω v).mpr (hω v))

end S33PF

theorem _root_.AlgebraicCurve.regularDiffs_eq_regularDifferentials_of_perfectField {K F : Type*}
  [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.regularDiffs K F = AlgebraicCurve.regularDifferentials K F := by
  exact S33PF.regularDiffs_eq
end AlgebraicCurves.Differentials.Proofs.RegularDiffs_eq_regularDifferentials_of_perfectField
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

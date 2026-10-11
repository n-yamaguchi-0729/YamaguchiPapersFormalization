/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.Place_ordDiff_eq_ord_diffCoeff
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional

/-!
# Place ord Diff eq ord Differential
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ordDiff_eq_ordDifferential
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
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve IntermediateField

theorem _root_.AlgebraicCurve.Place.ordDiff_eq_ordDifferential {K F : Type*} [Field K] [Field F]
  [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by
  have : PerfectField K := inferInstance
  have : v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver v
  obtain ⟨x, -, hfin, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := K) (F := F)).mp
      inferInstance
  have := hfin
  have : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite K⟮x⟯ F
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  have hπ₀ : v.ord ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F) =
    1 :=
    v.ord_coe_irreducible hirr
  have hd : v.dCoord = KaehlerDifferential.D K F
      ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F) := rfl
  have hω : ω = v.differentialCoeff ω • KaehlerDifferential.D K F
      ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F) := by
    rw [← hd, v.differentialCoeff_smul_dCoord]
  rw [AlgebraicCurve.Place.ordDiff_eq_ord_diffCoeff x v hπ₀ ω]
  change _ = v.ord (v.differentialCoeff ω)
  conv_lhs => rw [hω]
  rw [AlgebraicCurve.Place.diffCoeff_smul_D_eq x v (by rw [hπ₀]; exact one_ne_zero)]
end AlgebraicCurves.Places.Proofs.Place_ordDiff_eq_ordDifferential
end ProofImplementation

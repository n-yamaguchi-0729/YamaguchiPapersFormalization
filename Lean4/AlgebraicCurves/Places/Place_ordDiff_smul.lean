/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_ne_zero
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq
import AlgebraicCurves.Places.Place_exists_ord_eq_one

/-!
# Place ord Diff smul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ordDiff_smul
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

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace FF2R4A
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section R3grade
variable [CharZero K] (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
theorem ordDiff_smul (v : Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have h1 : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt v.exists_ord_eq_one]; exact one_ne_zero
  set a := Place.diffCoeff v.uniformizer_alt ω with ha
  have hωa : a • D K F v.uniformizer_alt = ω := Place.diffCoeff_smul_D_of_ord_ne_zero x v h1 ω
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hωa; exact hω hωa.symm
  rw [Place.ordDiff_def, Place.ordDiff_def, ← ha, ← hωa, smul_smul,
    Place.diffCoeff_smul_D_eq x v h1, v.ord_mul hg ha0]

end R3grade

end AlgebraicCurve.FF2R4A

end

theorem _root_.AlgebraicCurve.Place.ordDiff_smul {K F : Type*} [Field K] [Field F] [Algebra K F]
  [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω :=
  AlgebraicCurve.FF2R4A.ordDiff_smul x v hg hω
end AlgebraicCurves.Places.Proofs.Place_ordDiff_smul
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Place_isSeparable_adjoin_of_ord_eq_one
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental
import Nyll.AlgebraicCurves.Places.Place_transcendental_of_ord_ne_zero
import Nyll.AlgebraicCurves.Places.Place_exists_ord_eq_one
import Nyll.AlgebraicCurves.Differentials.Basic

/-!
# Place ord Diff zero of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ordDiff_zero_of_perfectField
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

open AlgebraicCurve

private theorem ordDiff_smul_D_uniformizer {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) (g : F) :
    v.ordDiff (g • KaehlerDifferential.D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have := Place.isSeparable_adjoin_of_ord_eq_one x v h1
  have hD : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K v.uniformizer_alt
      (v.transcendental_of_ord_ne_zero (h1 ▸ one_ne_zero))
  rw [Place.ordDiff_def, smul_left_injective F hD (Place.diffCoeff_smul_D ⟨g, rfl⟩)]

theorem _root_.AlgebraicCurve.Place.ordDiff_zero_of_perfectField {K F : Type*} [Field K] [Field F]
  [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 0

end
end AlgebraicCurves.Places.Proofs.Place_ordDiff_zero_of_perfectField
end ProofImplementation

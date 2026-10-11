/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Place_isSeparable_adjoin_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_isSeparable

/-!
# Place ord diff Coeff D nonneg of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_diffCoeff_D_nonneg_of_perfectField

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.mem_fiberOver
attribute [-simp] AlgebraicCurve.Place.fiberEquiv_symm_apply
attribute [-simp] AlgebraicCurve.Place.fiberEquiv_apply
attribute [-simp] AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
attribute [-simp] AlgebraicCurve.Divisor.pushforward_single
attribute [-simp] AlgebraicCurve.Place.coe_restrictInclusion
attribute [-simp] AlgebraicCurve.Place.mem_fiber
attribute [-simp] AlgebraicCurve.Place.restrict_toValuationSubring
attribute [-simp] AlgebraicCurve.Divisor.degree_pushforward
attribute [-simp] AlgebraicCurve.Place.restrictResidueMap_residue
attribute [-simp] AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
attribute [-simp] AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
theorem _root_.AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField {K F : Type*} [Field K]
  [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F}
    (ht : v.ord t = 1) {f : F} (hf : 0 ≤ v.ord f) :
    0 ≤ v.ord (AlgebraicCurve.Place.diffCoeff t (KaehlerDifferential.D K F f)) := by
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  have := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  exact AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable x v ht hf
end AlgebraicCurves.Places.Proofs.Place_ord_diffCoeff_D_nonneg_of_perfectField
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_eq_one

/-!
# Place derivation apply eq diff Coeff D mul
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_derivation_apply_eq_diffCoeff_D_mul
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

open AlgebraicCurve KaehlerDifferential

theorem _root_.AlgebraicCurve.Place.derivation_apply_eq_diffCoeff_D_mul
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (δ : Derivation K F F) (f : F) :
    δ f = Place.diffCoeff t (KaehlerDifferential.D K F f) * δ t :=
  calc δ f = δ.liftKaehlerDifferential (KaehlerDifferential.D K F f) :=
        (Derivation.liftKaehlerDifferential_comp_D δ f).symm
    _ = δ.liftKaehlerDifferential
          (Place.diffCoeff t (KaehlerDifferential.D K F f) • KaehlerDifferential.D K F t) := by
        rw [Place.diffCoeff_smul_D_of_ord_eq_one x v ht]
    _ = Place.diffCoeff t (KaehlerDifferential.D K F f) * δ t := by
        rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul]
end AlgebraicCurves.Places.Proofs.Place_derivation_apply_eq_diffCoeff_D_mul
end ProofImplementation

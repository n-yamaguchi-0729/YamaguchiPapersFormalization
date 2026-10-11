/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_norm_algebraMap_sub_eq_minpoly_eval

/-!
# Algebra norm algebra Map sub eq eval minpoly pow
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
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
  instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  instSMulAlgEquiv
  instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  instAlgebraSubtypeMemValuationSubringToValuationSubring
  instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring

open Polynomial

theorem _root_.Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) (c : K) :
    Algebra.norm K (algebraMap K L c - x)
      = ((minpoly K x).eval c) ^ (Module.finrank K L / (minpoly K x).natDegree) := by
  have hx : IsIntegral K x := .of_finite K x
  have hmin : minpoly K (IntermediateField.AdjoinSimple.gen K x) = minpoly K x :=
    IntermediateField.minpoly_gen K x
  have hfinE : Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) = (minpoly K
    x).natDegree :=
    IntermediateField.adjoin.finrank hx
  have hdeg : (minpoly K (IntermediateField.AdjoinSimple.gen K x)).natDegree
      = Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) := by
    rw [hmin, hfinE]
  have h1 : Algebra.norm K (algebraMap K (IntermediateField.adjoin K ({x} : Set L)) c
      - IntermediateField.AdjoinSimple.gen K x) = (minpoly K x).eval c := by
    rw [Algebra.norm_algebraMap_sub_eq_minpoly_eval _ hdeg c, hmin]
  have h2 : algebraMap (IntermediateField.adjoin K ({x} : Set L)) L
      (algebraMap K (IntermediateField.adjoin K ({x} : Set L)) c
        - IntermediateField.AdjoinSimple.gen K x) = algebraMap K L c - x := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hn : Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L
      = Module.finrank K L / (minpoly K x).natDegree := by
    have hmul := Module.finrank_mul_finrank K (IntermediateField.adjoin K ({x} : Set L)) L
    rw [hfinE] at hmul
    rw [← hmul, Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hx)]
  rw [← h2, ← Algebra.norm_norm (S := IntermediateField.adjoin K ({x} : Set L)),
    Algebra.norm_algebraMap, map_pow, h1, hn]

end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
end ProofImplementation

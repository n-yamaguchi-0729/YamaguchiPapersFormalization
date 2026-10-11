/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_algebraMap_sub_eq_minpoly_eval.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Norm.Transitivity
import Nyll.AlgebraicCurves.Places.OverDVR

/-!
# Algebra norm algebra Map sub eq minpoly eval
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_minpoly_eval

open Polynomial IntermediateField

namespace S09NR

section Norm

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [Module.Finite F F']

theorem norm_algebraMap_sub (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F F') (c : F)
  :
    Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
  set y := x - algebraMap F F' c with hy
  have hyint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hminy : minpoly F y = (minpoly F x).comp (X + C c) := minpoly.sub_algebraMap x c
  have hdegy : (minpoly F y).natDegree = Module.finrank F F' := by
    rw [hminy, natDegree_comp, natDegree_X_add_C, mul_one, hdeg]
  have htower : Module.finrank F F' = Module.finrank F F⟮y⟯ * Module.finrank F⟮y⟯ F' :=
    (Module.finrank_mul_finrank F F⟮y⟯ F').symm
  rw [adjoin.finrank hyint, hdegy] at htower
  have hn : 0 < Module.finrank F F' := Module.finrank_pos
  have hm : Module.finrank F⟮y⟯ F' = 1 := by
    have h : Module.finrank F F' * Module.finrank F⟮y⟯ F' = Module.finrank F F' * 1 := by
      rw [mul_one]; exact htower.symm
    exact Nat.eq_of_mul_eq_mul_left hn h
  have hnormy : Algebra.norm F y = (-1) ^ Module.finrank F F' * (minpoly F x).eval c := by
    rw [Algebra.norm_eq_norm_adjoin, hm, pow_one, ← adjoin.powerBasis_gen hyint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_gen, minpoly_gen,
        adjoin.powerBasis_dim,
      hdegy, hminy, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  have hneg : algebraMap F F' c - x = algebraMap F F' (-1) * y := by
    rw [map_neg, map_one, neg_one_mul, hy, neg_sub]
  rw [hneg, map_mul, Algebra.norm_algebraMap, hnormy, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow,
    one_mul]

end Norm

section Ord

open AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F']
  [Module.Finite F F']

theorem ord_norm_sub_eq (v : Place K F) (Q : Polynomial v.toValuationSubring) {x : F'}
    (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x)
    (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) :
    v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring)
      : F) := by
  have h1 : x - algebraMap F F' (b : F) = -(algebraMap F F' (b : F) - x) := (neg_sub _ _).symm
  have h2 : Algebra.norm F (-(algebraMap F F' (b : F) - x))
      = (-1) ^ Module.finrank F F' * Algebra.norm F (algebraMap F F' (b : F) - x) := by
    have hneg1 : (-1 : F') = algebraMap F F' (-1) := by simp
    rw [neg_eq_neg_one_mul, map_mul, hneg1, Algebra.norm_algebraMap]
  have h3 : ((Q.eval b : v.toValuationSubring) : F) = (minpoly F x).eval (b : F) := by
    rw [← hQ, eval_map]
    exact (eval₂_at_apply (algebraMap v.toValuationSubring F) b).symm
  rw [h1, h2, norm_algebraMap_sub x hdeg, h3]
  rcases neg_one_pow_eq_or F (Module.finrank F F') with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Place.ord_neg]

end Ord

end S09NR

theorem _root_.Algebra.norm_algebraMap_sub_eq_minpoly_eval {F F' : Type*} [Field F] [Field F']
  [Algebra F F'] [Module.Finite F F'] (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F
  F') (c : F) : Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
  exact S09NR.norm_algebraMap_sub x hdeg c
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_minpoly_eval
end ProofImplementation

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

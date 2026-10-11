/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_weilReciprocity.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Rational.RationalFunctionField_weilReciprocity
import AlgebraicCurves.FunctionFields.WeilReciprocity_algebraMap
import AlgebraicCurves.FunctionFields.FunctionField_finite_of_ratFuncAlgHom
import AlgebraicCurves.FunctionFields.FunctionField_exists_ratFuncAlgHom_apply_X_eq
import AlgebraicCurves.Places.Place_isRational_of_isAlgClosed
import AlgebraicCurves.Places.Rational.RationalFunctionField_deg_eq_one_of_isAlgClosed
import AlgebraicCurves.Places.Place_isRational_iff_deg_eq_one
import AlgebraicCurves.Places.Rational.RationalFunctionField_hasPrincipalDivisors
import AlgebraicCurves.Places.Place_evalAt_algebraMap
import AlgebraicCurves.Places.Place_ord_algebraMap

/-!
# Weil Reciprocity
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.WeilReciprocity
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace WeilReciprocityAnchor
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finsupp_prod_zpow_const {c : K} (hc : c ≠ 0) (D : Divisor K F) :
    (D.prod fun _ n => c ^ n) = c ^ (D.sum fun _ n => n) := by
  classical
  unfold Finsupp.prod Finsupp.sum
  induction D.support using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

theorem degree_eq_sum_of_rational (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v hv => ?_
  rw [AddMonoidHom.mulRight_apply, (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).1 (hrat v hv),
    Nat.cast_one, mul_one]

end AlgebraicCurve.WeilReciprocityAnchor

open AlgebraicCurve.WeilReciprocityAnchor in
theorem _root_.AlgebraicCurve.weilReciprocity (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] : WeilReciprocity K F := by
  classical
  intro f g Df Dg hf hg hDf hDg hdisj hratf hratg
  by_cases hconst : g ∈ Set.range (algebraMap K F)
  · obtain ⟨c, rfl⟩ := hconst
    have hc : c ≠ 0 := fun h => hg (by rw [h, map_zero])
    have hDg0 : Dg = 0 := by
      ext v
      rw [hDg v, AlgebraicCurve.Place.ord_algebraMap, Finsupp.coe_zero, Pi.zero_apply]
    obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    have hDfD' : Df = D' := by
      ext v; rw [hDf v, hD' v]
    have hsum : (Df.sum fun _ n => n) = 0 := by
      rw [← degree_eq_sum_of_rational Df hratf, hDfD', hdeg]
    rw [hDg0, Divisor.evalFun_zero, Divisor.evalFun_def]
    rw [show (∏ v ∈ Df.support, Place.evalAt v (algebraMap K F c) ^ Df v)
        = Df.prod fun _ n => c ^ n from
      Finset.prod_congr rfl fun v _ => by rw [AlgebraicCurve.Place.evalAt_algebraMap]]
    rw [finsupp_prod_zpow_const hc, hsum, zpow_zero]
  · obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq hconst
    have finφ : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule :=
      AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom φ
    let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
    have stφ : @IsScalarTower K (RatFunc K) F _ algφ.toSMul _ :=
      @IsScalarTower.of_algebraMap_eq K (RatFunc K) F _ _ _ _ algφ _ fun x => (φ.commutes x).symm
    have : CharZero (RatFunc K) :=
      charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
    have algc : @Algebra.IsAlgebraic (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.of_finite (RatFunc K) F _ _ _ algφ finφ
    have sepφ : @Algebra.IsSeparable (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.isSeparable_of_perfectField (RatFunc K) F _ _ algφ algc _
    have : HasPrincipalDivisors K (RatFunc K) :=
      AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors K
    have hXg : @algebraMap (RatFunc K) F _ _ algφ RatFunc.X = g := hφ
    have hratF : ∀ v : Place K (RatFunc K), v.IsRational := fun v =>
      (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).2
        (AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed K v)
    have hratAll : ∀ w : Place K F, w.IsRational := fun w =>
      @AlgebraicCurve.Place.isRational_of_isAlgClosed K F _ _ _ _ algφ stφ finφ w
    have key := @AlgebraicCurve.weilReciprocity_algebraMap K (RatFunc K) F _ _ _ _ _ algφ stφ finφ
      sepφ
      _ _ _ (AlgebraicCurve.RationalFunctionField.weilReciprocity K) f RatFunc.X hf
        RatFunc.X_ne_zero
      Df Dg hDf (fun w =>
        by rw [hDg w, ← hXg]) (fun w => by rw [← hXg] at hdisj; exact hdisj w) hratf hratF
      (fun v _ w _ => hratAll w)
    rw [hXg] at key
    exact key
end AlgebraicCurves.Geometry.Proofs.WeilReciprocity
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.ConstantExtension
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Places.Place_exists_finite_constantField_form_fiberConstants_eq_singleton
import AlgebraicCurves.Places.Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension

/-!
# Divisor exists finite constant Field form pullback Constants eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_exists_finite_constantField_form_pullbackConstants_eq
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open _root_.AlgebraicCurve

universe u v

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Divisor
open _root_.AlgebraicCurve.Divisor
namespace ExistsFiniteConstantFieldFormAux
open _root_.AlgebraicCurve.Divisor
open _root_.AlgebraicCurve

theorem isAlgebraic_of_forall_pow_pow_eq (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (ℓ : ℕ) [Fact ℓ.Prime] (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) :
    Algebra.IsAlgebraic K K' := by
  refine ⟨fun a => ?_⟩
  obtain ⟨n, hn, ha⟩ := halg a
  refine ⟨Polynomial.X ^ ℓ ^ n - Polynomial.X, ?_, ?_⟩
  · exact FiniteField.X_pow_card_pow_sub_X_ne_zero K hn.ne' (Fact.out : ℓ.Prime).one_lt
  · simp only [map_sub, map_pow, Polynomial.aeval_X, ha, sub_self]

theorem mem_range_of_isAlgebraic_of_constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hC : ConstantsAreBase K F) (y : F) (hy : IsAlgebraic K y) : y ∈ (algebraMap K F).range := by
  have hint : IsIntegral K y := hy.isIntegral
  have hmem : y ∈ LSpace (0 : Divisor K F) := by
    intro v
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    refine v.adicValuation_le_one_of_mem ?_
    have hint' : IsIntegral v.toValuationSubring y := hint.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
    rw [← hz]
    exact z.2
  have hC' : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [hC'] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  exact ⟨c, hc⟩

end AlgebraicCurve.Divisor.ExistsFiniteConstantFieldFormAux

open AlgebraicCurve.Divisor.ExistsFiniteConstantFieldFormAux in
theorem _root_.AlgebraicCurve.Divisor.exists_finite_constantField_form_pullbackConstants_eq
    (K' : Type u) (F' : Type v) [Field K'] [Field F'] [Algebra K' F']
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K' ℓ]
    (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a)
    (hfg : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F'] (hC : ConstantsAreBase K' F') (c : Divisor K' F') :
    ∃ (K : Type u) (F : Type v) (_ : Field K) (_ : Finite K) (_ : Field F)
      (_ : Algebra K K') (_ : Algebra K F) (_ : Algebra F F') (_ : Algebra K F')
      (_ : IsScalarTower K K' F') (_ : IsScalarTower K F F') (_ : Algebra.IsIntegral F F')
      (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F)
      (D : Divisor K F),
        Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤ ∧
        ConstantsAreBase K F ∧
        Divisor.pullbackConstants K' F' D = c ∧ Divisor.degree D = Divisor.degree c := by
  obtain ⟨K, F, iFK, iFinK, iFF, iAKK', iAKF, iAFF', iAKF', iST1, iST2, iInt, iCurve, iEFT,
      hgen, hconst, hW⟩ :=
    Place.exists_finite_constantField_form_fiberConstants_eq_singleton K' F' ℓ halg hfg hC c.support
  have : Algebra.IsAlgebraic K K' := isAlgebraic_of_forall_pow_pow_eq K K' ℓ halg
  have : PerfectField K := inferInstance
  have : Algebra.IsSeparable K K' := inferInstance
  have hconstK : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range :=
    fun y hy => mem_range_of_isAlgebraic_of_constantsAreBase hconst y hy
  have he : ∀ w : Place K' F', (Place.forgetConstants (K := K) w).ramificationIndex F = 1 :=
    fun w => Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension hgen
      hconstK w
  have hfib : ∀ w ∈ c.support, ∀ w' : Place K' F',
      Place.restrictConstants F (K := K) w' = Place.restrictConstants F (K := K) w → w' = w := by
    intro w hw w' h
    have hmem : w' ∈ Place.fiberConstants K' F' (Place.restrictConstants F (K := K) w) :=
      Place.mem_fiberConstants.mpr h
    rw [(hW w hw).1] at hmem
    exact Finset.mem_singleton.mp hmem
  set D : Divisor K F :=
    ∑ w ∈ c.support, Finsupp.single (Place.restrictConstants F (K := K) w) (c w) with hD
  have hDapply : ∀ w' : Place K' F', D (Place.restrictConstants F (K := K) w') = c w' := by
    intro w'
    rw [hD, Finsupp.finsetSum_apply]
    by_cases hw' : w' ∈ c.support
    · rw [Finset.sum_eq_single_of_mem
        (f := fun w => Finsupp.single (Place.restrictConstants F (K := K) w) (c w)
          (Place.restrictConstants F (K := K) w')) w' hw' ?_]
      · exact Finsupp.single_eq_same
      · intro w hw hne
        refine Finsupp.single_apply_eq_zero.mpr fun h => ?_
        have hww : w' = w := hfib w hw w' (h ▸ rfl)
        exact absurd hww.symm hne
    · rw [Finsupp.notMem_support_iff.mp hw']
      refine Finset.sum_eq_zero fun w hw => Finsupp.single_apply_eq_zero.mpr fun h => ?_
      have hww : w' = w := hfib w hw w' (h ▸ rfl)
      subst hww
      exact absurd hw hw'
  have hpull : Divisor.pullbackConstants K' F' D = c := by
    ext w'
    rw [Divisor.pullbackConstants_apply, he w', hDapply w', Nat.cast_one, one_mul]
  have hdeg : Divisor.degree D = Divisor.degree c := by
    have hc : (∑ w ∈ c.support, Finsupp.single w (c w)) = c := by
      simpa only [Finsupp.sum] using Finsupp.sum_single c
    conv_rhs => rw [← hc]
    rw [hD, map_sum, map_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Divisor.degree_single, Divisor.degree_single, (hW w hw).2]
  exact ⟨K, F, iFK, iFinK, iFF, iAKK', iAKF, iAFF', iAKF', iST1, iST2, iInt, iCurve, iEFT, D,
    hgen, hconst, hpull, hdeg⟩
end AlgebraicCurves.Divisors.Proofs.Divisor_exists_finite_constantField_form_pullbackConstants_eq
end ProofImplementation

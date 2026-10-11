/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_not_mem_and_forall_ne_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import Nyll.AlgebraicCurves.Geometry.One_le_deg

/-!
# Place exists not mem and forall ne mem

Distinct places separate valuation-subring membership: a function can be excluded from one place
while belonging to each place in a finite collection of others.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_not_mem_and_forall_ne_mem
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.adicValuation_le_one_iff_mem (v : Place K F) {f : F} :
    v.adicValuation f ≤ 1 ↔ f ∈ v.toValuationSubring := by
  refine ⟨fun h => ?_, v.adicValuation_le_one_of_mem⟩
  by_contra hf
  have hf0 : f ≠ 0 := fun h0 => hf (h0 ▸ v.toValuationSubring.zero_mem)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hmax : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hf
    have h1 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) * f⁻¹ = 1 := by
      have h := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using h
    have h2 : (((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring) : F) = f := by
      rw [eq_inv_of_mul_eq_one_left h1, inv_inv]
    rw [← h2]
    exact SetLike.coe_mem _
  have hlt : v.adicValuation f⁻¹ < 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v.heightOneSpectrum
      (⟨f⁻¹, hinv⟩ : v.toValuationSubring)).mpr (by rwa [heightOneSpectrum_asIdeal])
    rwa [← v.adicValuation_coe] at this
  rw [map_inv₀] at hlt
  have hpos : 0 < v.adicValuation f := zero_lt_iff.mpr (v.adicValuation_ne_zero hf0)
  have : 1 < v.adicValuation f := (inv_lt_one₀ hpos).mp hlt
  exact absurd h (not_le.mpr this)

open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place

open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem
    {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : AlgebraicCurve.ConstantsAreBase K F) (v : AlgebraicCurve.Place K F) :
    ∃ f : F, f ∉ v.toValuationSubring ∧
      ∀ w : AlgebraicCurve.Place K F, w ≠ v → f ∈ w.toValuationSubring := by
  classical
  obtain ⟨_, hfin0, γ, D₀, hR⟩ :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hC
  set n : ℕ := γ.toNat + 1 with hn
  set D : Divisor K F := Finsupp.single v (n : ℤ) with hD
  have hdeg : Divisor.degree D = (n : ℤ) * v.deg := Divisor.degree_single v n
  have hvdeg : (1 : ℤ) ≤ v.deg := by exact_mod_cast AlgebraicCurve.one_le_deg v
  have hmax := hR.isMax D
  have hnγ : γ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat γ
    simp only [hn]; push_cast; omega
  have hell : (2 : ℤ) ≤ (ell D : ℤ) := by
    have : (n : ℤ) ≤ Divisor.degree D := by rw [hdeg]; nlinarith
    linarith
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  have hnot : ¬ (LSpace D ≤ LSpace (0 : Divisor K F)) := by
    intro hle
    have := hfin0
    have hle' : Module.finrank K (LSpace D) ≤ Module.finrank K (LSpace (0 : Divisor K F)) :=
      LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
        (Submodule.inclusion_injective hle)
    have : (ell D : ℤ) ≤ (ell (0 : Divisor K F) : ℤ) := by exact_mod_cast hle'
    rw [hell0] at this
    push_cast at this
    linarith
  obtain ⟨f, hfD, hf0⟩ := Set.not_subset.mp hnot
  have hfD' : f ∈ LSpace D := hfD
  refine ⟨f, ?_, ?_⟩
  · intro hfv
    apply hf0
    change f ∈ LSpace (0 : Divisor K F)
    intro w
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    by_cases hw : w = v
    · subst hw; exact w.adicValuation_le_one_of_mem hfv
    · have h := hfD' w
      have hDw : D w = 0 := by rw [hD, Finsupp.single_apply, ite_eq_right (Ne.symm hw)]
      rwa [hDw, WithZero.exp_zero] at h
  · intro w hw
    have h := hfD' w
    have hDw : D w = 0 := by rw [hD, Finsupp.single_apply, ite_eq_right (Ne.symm hw)]
    rw [hDw, WithZero.exp_zero] at h
    exact (w.adicValuation_le_one_iff_mem).mp h
end AlgebraicCurves.Places.Proofs.Place_exists_not_mem_and_forall_ne_mem
end ProofImplementation

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

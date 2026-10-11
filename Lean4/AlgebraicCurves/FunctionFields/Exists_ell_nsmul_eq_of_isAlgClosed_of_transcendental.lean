/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.IsCurveOver_of_isAlgClosed_of_transcendental
import AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed_of_transcendental
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_of_genusReached
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
import AlgebraicCurves.Cohomology.RiemannRoch.RiemannGenusReachedAt_eq_of_ge
import AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1

/-!
# Exists ell nsmul eq of is Alg Closed of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
attribute [-simp] AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ell (0 : Divisor K F) = 1 ∧
    ∃ M : ℕ, 1 ≤ M ∧ ∀ N, M ≤ N →
      (ell (N • D) : ℤ) = N * Divisor.degree D + 1 - genusFF K F := by
  classical
  have hICO : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental x hx
  have hEFT : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx inferInstance
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  refine ⟨hell0, ?_⟩
  obtain ⟨hNon, hFD, γ, D₀, hRGA⟩ := stichtenothGenusExists_of_isCurveOver hC
  have : Nonempty (Place K F) := hNon
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hFD
  have hidx0 : (indexOfSpecialty (0 : Divisor K F) : ℤ)
      = (ell (0 : Divisor K F) : ℤ) - (Divisor.degree (0 : Divisor K F) + 1 - γ) :=
    (indexOfSpecialty_eq_of_genusReached hRGA 0).2
  have hγ : γ = (genusFF K F : ℤ) := by
    have hgFF : indexOfSpecialty (0 : Divisor K F) = genusFF K F := by
      rw [indexOfSpecialty_eq_finrank_H1]; rfl
    have hdeg0 : Divisor.degree (0 : Divisor K F) = 0 := map_zero _
    rw [hgFF, hdeg0, hell0] at hidx0
    push_cast at hidx0
    linarith
  have hDnn : ∀ v, 0 ≤ D v := fun v ↦ by rw [hD v]; exact le_max_left 0 _
  have hDne : D ≠ 0 := by
    intro h0
    have hxmem : x ∈ LSpace (0 : Divisor K F) := by
      rw [mem_lSpace_iff_ord]
      right
      intro v
      have hDv0 : max 0 (-v.ord x) = 0 := by
        have := hD v; rw [h0] at this; exact this.symm
      have : -v.ord x ≤ 0 := max_eq_left_iff.mp hDv0
      simpa using neg_nonpos.mp this
    rw [hC] at hxmem
    obtain ⟨a, ha⟩ := hxmem
    exact hx (ha ▸ isAlgebraic_algebraMap a)
  obtain ⟨Q, hQ⟩ := Finsupp.support_nonempty_iff.mpr hDne
  have hDQ : 1 ≤ D Q := by
    have hne : D Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
    have hnn := hDnn Q
    omega
  obtain ⟨n₀, hRGAQ⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hRGA Q
  refine ⟨max 1 n₀, le_max_left _ _, fun N hN ↦ ?_⟩
  have hNn₀ : n₀ ≤ N := (le_max_right _ _).trans hN
  have hle : (n₀ : ℤ) • Finsupp.single Q (1 : ℤ) ≤ N • D := by
    intro v
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply,
      nsmul_eq_mul]
    split_ifs with h
    · subst h
      calc (n₀ : ℤ) * 1 = (n₀ : ℤ) := mul_one _
        _ ≤ (N : ℤ) := by exact_mod_cast hNn₀
        _ = (N : ℤ) * 1 := (mul_one _).symm
        _ ≤ (N : ℤ) * D Q := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hDQ) (Nat.cast_nonneg N)
    · calc (n₀ : ℤ) * 0 = 0 := mul_zero _
        _ ≤ (N : ℤ) * D v := mul_nonneg (Nat.cast_nonneg N) (hDnn v)
  have heq : Divisor.degree (N • D) - (ell (N • D) : ℤ) = γ - 1 :=
    hRGAQ.eq_of_ge hle
  have hdegNsmul : Divisor.degree (N • D) = (N : ℤ) * Divisor.degree D := by
    rw [AddMonoidHom.map_nsmul, nsmul_eq_mul]
  rw [hdegNsmul, hγ] at heq
  linarith
end AlgebraicCurves.FunctionFields.Proofs.Exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
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
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_genus_riemannIndex_of_isCurveOver
import AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.Ell_eq_zero_of_degree_neg

/-!
Equality of the function-field genus from equality of the Riemann--Roch dimension differences.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Eq_genusFF_of_forall_ell_sub_ell_eq
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt) in
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
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

universe u v

open AlgebraicCurve

theorem _root_.AlgebraicCurve.eq_genusFF_of_forall_ell_sub_ell_eq
    {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F)
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    g = genusFF K F := by
  obtain ⟨γ, hγ⟩ := exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) hC
  have star : ∀ D : Divisor K F, (indexOfSpecialty D : ℤ) = γ - g + ell (Kc - D) := by
    intro D
    have h1 := (hγ D).2
    have h2 := hRR D
    linarith
  obtain ⟨⟨Q⟩, hfin, γ₀, D₀, hreach⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hC
  have : Nonempty (Place K F) := ⟨Q⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := hfin
  obtain ⟨n, hn⟩ := exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached hreach Q
  have hle : γ ≤ g := by
    have h := star ((n : ℤ) • Finsupp.single Q 1)
    rw [hn] at h
    have h' : (0 : ℤ) ≤ ell (Kc - (n : ℤ) • Finsupp.single Q 1) := Int.natCast_nonneg _
    push_cast at h
    linarith
  have : Module.Finite K Q.ResidueField := IsCurveOver.finiteResidue Q
  have hdeg : 0 < (Q.deg : ℤ) := by
    have : 0 < Module.finrank K Q.ResidueField := Module.finrank_pos
    exact_mod_cast this
  have hvan : ell (Kc - (Kc + Finsupp.single Q 1)) = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [sub_add_cancel_left, map_neg, Divisor.degree_single]
    linarith
  have hge : (g : ℤ) ≤ γ := by
    have h := star (Kc + Finsupp.single Q 1)
    rw [hvan] at h
    have h' : (0 : ℤ) ≤ indexOfSpecialty (Kc + Finsupp.single Q 1) := Int.natCast_nonneg _
    push_cast at h
    linarith
  have hγg : γ = g := le_antisymm hle hge
  have hi0 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = γ := by
    have h := (hγ 0).2
    rw [ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
    push_cast at h
    linarith
  have hH1 : indexOfSpecialty (0 : Divisor K F) = genusFF K F :=
    indexOfSpecialty_eq_finrank_H1 (0 : Divisor K F)
  have : (g : ℤ) = genusFF K F := by rw [← hH1, hi0, hγg]
  exact_mod_cast this
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Eq_genusFF_of_forall_ell_sub_ell_eq
end ProofImplementation

open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt) in
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
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

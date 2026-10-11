/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_not_mem_range_and_forall_ne_ord_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Geometry.Exists_int_forall_degree_add_one_sub_le_ell

/-!
# Place exists not mem range and forall ne ord nonneg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_not_mem_range_and_forall_ne_ord_nonneg
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

noncomputable section

universe u v

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_not_mem_range_and_forall_ne_ord_nonneg
    (K : Type u) (F : Type v) [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] (P : Place K F) :
    ∃ y : F, y ∉ Set.range (algebraMap K F) ∧ ∀ Q : Place K F, Q ≠ P → 0 ≤ Q.ord y := by
  classical
  obtain ⟨γ, hγ⟩ := AlgebraicCurve.exists_int_forall_degree_add_one_sub_le_ell K F
  have : Module.Finite K P.ResidueField := IsCurveOver.finiteResidue P
  have hdeg : (1 : ℤ) ≤ (P.deg : ℤ) := by
    have : 0 < P.deg := Module.finrank_pos
    exact_mod_cast this
  set N : ℕ := γ.toNat + 1 with hN
  have hNγ : γ + 1 ≤ (N : ℤ) := by
    have := Int.self_le_toNat γ
    simp only [hN]; push_cast; omega
  set D : Divisor K F := Finsupp.single P (N : ℤ) with hD
  have hdegD : Divisor.degree D = (N : ℤ) * P.deg := by rw [hD, Divisor.degree_single]
  have hell : (2 : ℤ) ≤ (ell D : ℤ) := by
    have h1 := hγ D
    rw [hdegD] at h1
    have h2 : (N : ℤ) ≤ (N : ℤ) * P.deg := by nlinarith
    omega
  have hnot : ¬ (LSpace D ≤ Submodule.span K {(1 : F)}) := by
    intro hle
    have hfin : Module.finrank K ↥(LSpace D) ≤ Module.finrank K ↥(Submodule.span K {(1 : F)}) :=
      Submodule.finrank_mono hle
    have h1 : Module.finrank K ↥(Submodule.span K {(1 : F)}) = 1 := finrank_span_singleton
      one_ne_zero
    have : (ell D : ℤ) ≤ 1 := by
      change ((Module.finrank K ↥(LSpace D) : ℕ) : ℤ) ≤ 1
      exact_mod_cast (h1 ▸ hfin)
    omega
  obtain ⟨y, hyD, hy1⟩ := Set.not_subset.mp hnot
  have hy0 : y ≠ 0 := fun h => hy1 (by rw [h]; exact Submodule.zero_mem _)
  refine ⟨y, ?_, ?_⟩
  · rintro ⟨c, rfl⟩
    apply hy1
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  · intro Q hQ
    rcases (mem_lSpace_iff_ord.mp hyD) with h | h
    · exact absurd h hy0
    · have := h Q
      rw [hD, Finsupp.single_eq_of_ne hQ] at this
      simpa using this

end
end AlgebraicCurves.Places.Proofs.Place_exists_not_mem_range_and_forall_ne_ord_nonneg
end ProofImplementation

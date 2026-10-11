/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Cech.Maps
import AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver

/-!
# Pullback Along mem regular Differentials of mem of is Curve Over
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace PullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
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

open AlgebraicCurve
open scoped Pointwise

namespace RegPull

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_inv_smul_iff (w : F ≃ₐ[K] F) (v : Place K F) (f : F) :
    f ∈ (w⁻¹ • v).toValuationSubring ↔ w f ∈ v.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
    AlgEquiv.smul_def]

theorem exists_mem_D_eq_smul_dCoord [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F g = c • v.dCoord := by
  have key : ∀ u : F, u ≠ 0 → v.ord u = 0 →
      ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F u = c • v.dCoord := by
    intro u hu0 hu
    refine ⟨v.differentialCoeff (KaehlerDifferential.D K F u), ?_, (v.differentialCoeff_smul_dCoord
      _).symm⟩
    rcases localUnitDerivativeRegular_of_isCurveOver v u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact v.mem_toValuationSubring_of_ord_nonneg h
  set a : v.toValuationSubring := ⟨g, hg⟩ with ha
  by_cases hunit : IsUnit a
  · have hord : v.ord g = 0 := by
      have := v.ord_coe_unit hunit.unit
      rwa [IsUnit.unit_spec] at this
    have hg0 : g ≠ 0 := by
      intro h0
      apply hunit.ne_zero
      exact Subtype.ext h0
    exact key g hg0 hord
  · have h1 : IsUnit (1 + a) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-a) with h | h
      · exact absurd (IsUnit.neg_iff _ |>.mp h) hunit
      · simpa using h
    have hord : v.ord (1 + g) = 0 := by
      have := v.ord_coe_unit h1.unit
      rwa [IsUnit.unit_spec] at this
    have hne : (1 + g) ≠ 0 := by
      intro h0
      apply h1.ne_zero
      exact Subtype.ext h0
    obtain ⟨c, hc, hcD⟩ := key (1 + g) hne hord
    refine ⟨c, hc, ?_⟩
    rw [← hcD, map_add, Derivation.map_one_eq_zero, zero_add]

theorem main [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ v : Place K F, v.DCoordGenerates]
    (w : F ≃ₐ[K] F) {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) :
    Differential.pullbackAlong (w : F →ₐ[K] F) ω ∈ regularDifferentials K F := by
  rw [mem_regularDifferentials_iff] at hω ⊢
  intro v
  obtain ⟨f, hf, hωf⟩ := hω (w⁻¹ • v)
  obtain ⟨π, hπ1, hπd⟩ := (w⁻¹ • v).exists_ord_eq_one_and_dCoord_eq
  have hwf : w f ∈ v.toValuationSubring := (mem_inv_smul_iff w v f).mp hf
  have hπmem : π ∈ (w⁻¹ • v).toValuationSubring :=
    (w⁻¹ • v).mem_toValuationSubring_of_ord_nonneg (by rw [hπ1]; exact zero_le_one)
  have hwπ : w π ∈ v.toValuationSubring := (mem_inv_smul_iff w v π).mp hπmem
  obtain ⟨c, hc, hcD⟩ := exists_mem_D_eq_smul_dCoord v hwπ
  refine ⟨w f * c, mul_mem hwf hc, ?_⟩
  rw [hωf, hπd, Differential.pullbackAlong_smul, Differential.pullbackAlong_D,
    AlgEquiv.coe_toAlgHom, hcD,
    mul_smul]

end RegPull

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (w : F ≃ₐ[K] F) {ω : Ω[F⁄K]} (hω : ω ∈ AlgebraicCurve.regularDifferentials K F) :
    AlgebraicCurve.Differential.pullbackAlong (w : F →ₐ[K] F) ω ∈
      AlgebraicCurve.regularDifferentials K F :=
  RegPull.main w hω

end PullbackAlong_mem_regularDifferentials_of_mem_of_isCurveOver
end AlgebraicCurves.Differentials.Proofs
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.cechH1.traceAlong_mk
  AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply
  AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk
  AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

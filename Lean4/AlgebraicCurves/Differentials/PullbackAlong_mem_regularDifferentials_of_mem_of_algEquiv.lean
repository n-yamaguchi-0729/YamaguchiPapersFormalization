/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.Places.Place_mem_iff_ord_nonneg
import AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver

/-!
# Pullback Along mem regular Differentials of mem of alg Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace PullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
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

namespace RegPullIso

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_of_ord_nonneg {L : Type*} [Field L] [Algebra K L] (v : Place K L) {f : L} (h : 0 ≤
  v.ord f) :
    f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact (v.mem_iff_ord_nonneg hf).mpr h

/-- The place pulled back along an algebra isomorphism of function fields. -/
noncomputable def pullPlace (Φ : F ≃ₐ[K] F') (w : Place K F') : Place K F :=
  Place.congrRingEquiv (Φ.symm : F' ≃+* F) (fun a => by
    change Φ.symm (algebraMap K F' a) = algebraMap K F a
    exact Φ.symm.commutes a) w

theorem mem_pullPlace_iff (Φ : F ≃ₐ[K] F') (w : Place K F') (f : F) :
    f ∈ (pullPlace Φ w).toValuationSubring ↔ Φ f ∈ w.toValuationSubring := by
  rw [pullPlace, Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  exact Iff.rfl

theorem exists_mem_D_eq_smul_dCoord [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ w : Place K F', w.DCoordGenerates] (v : Place K F') {g : F'} (hg : g ∈ v.toValuationSubring)
      :
    ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F' g = c • v.dCoord := by
  have key : ∀ u : F', u ≠ 0 → v.ord u = 0 →
      ∃ c ∈ v.toValuationSubring, KaehlerDifferential.D K F' u = c • v.dCoord := by
    intro u hu0 hu
    refine ⟨v.differentialCoeff (KaehlerDifferential.D K F' u), ?_,
      (v.differentialCoeff_smul_dCoord _).symm⟩
    rcases localUnitDerivativeRegular_of_isCurveOver v u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact mem_of_ord_nonneg v h
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

theorem main [PerfectField K] [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ w : Place K F', w.DCoordGenerates]
    (Φ : F ≃ₐ[K] F') {η : Ω[F⁄K]} (hη : η ∈ regularDifferentials K F) :
    Differential.pullbackAlong (Φ : F →ₐ[K] F') η ∈ regularDifferentials K F' := by
  rw [mem_regularDifferentials_iff] at hη ⊢
  intro w
  obtain ⟨f, hf, hηf⟩ := hη (pullPlace Φ w)
  obtain ⟨π, hπ1, hπd⟩ := (pullPlace Φ w).exists_ord_eq_one_and_dCoord_eq
  have hwf : Φ f ∈ w.toValuationSubring := (mem_pullPlace_iff Φ w f).mp hf
  have hπmem : π ∈ (pullPlace Φ w).toValuationSubring :=
    mem_of_ord_nonneg (pullPlace Φ w) (by rw [hπ1]; exact zero_le_one)
  have hwπ : Φ π ∈ w.toValuationSubring := (mem_pullPlace_iff Φ w π).mp hπmem
  obtain ⟨c, hc, hcD⟩ := exists_mem_D_eq_smul_dCoord w hwπ
  refine ⟨Φ f * c, mul_mem hwf hc, ?_⟩
  rw [hηf, hπd, Differential.pullbackAlong_smul, Differential.pullbackAlong_D,
    AlgEquiv.coe_toAlgHom, hcD,
    mul_smul]

end RegPullIso

theorem _root_.AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
    {K : Type*} [Field K] [PerfectField K] {F F' : Type*} [Field F] [Field F'] [Algebra K F]
      [Algebra K F']
    [Algebra.EssFiniteType K F'] [IsCurveOver K F']
    [∀ v : Place K F, v.DCoordGenerates] [∀ w : Place K F', w.DCoordGenerates]
    (Φ : F ≃ₐ[K] F') (η : Ω[F⁄K]) (hη : η ∈ regularDifferentials K F) :
    Differential.pullbackAlong (Φ : F →ₐ[K] F') η ∈ regularDifferentials K F' :=
  RegPullIso.main Φ hη
end AlgebraicCurves.Differentials.Proofs.PullbackAlong_mem_regularDifferentials_of_mem_of_algEquiv
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

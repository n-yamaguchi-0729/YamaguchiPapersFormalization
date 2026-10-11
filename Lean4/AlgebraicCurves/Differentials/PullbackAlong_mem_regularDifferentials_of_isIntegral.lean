/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_pullbackAlong_mem_regularDifferentials_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver
import AlgebraicCurves.Places.Place_mem_comap_iff_ord_nonneg
import AlgebraicCurves.Places.Place_ord_add_eq_of_lt

/-!
# Pullback Along mem regular Differentials of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.PullbackAlong_mem_regularDifferentials_of_isIntegral
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

open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential

namespace PBRegSol

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) : f ∈ v.toValuationSubring ↔ 0 ≤
  v.ord f := by
  have h := AlgebraicCurve.Place.mem_comap_iff_ord_nonneg (F := F) (F' := F) (w := v) hf
  rw [ValuationSubring.mem_comap] at h
  exact h

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  by
  rcases eq_or_ne f 0 with rfl | h0
  · rw [v.ord_zero]
  · exact (mem_iff_ord_nonneg v h0).1 hf

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : 0 ≤ v.ord f) : f ∈ v.toValuationSubring :=
  by
  rcases eq_or_ne f 0 with rfl | h0
  · exact v.toValuationSubring.zero_mem
  · exact (mem_iff_ord_nonneg v h0).2 hf

theorem ord_neg_one (v : Place K F) : v.ord (-1 : F) = 0 := by
  have h := v.ord_mul (f := (-1 : F)) (g := (-1 : F)) (neg_ne_zero.2 one_ne_zero) (neg_ne_zero.2
    one_ne_zero)
  rw [neg_one_mul, neg_neg, v.ord_one] at h
  omega

theorem exists_D_eq_smul_dCoord [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (w : Place K F) {g : F} (hg : g ∈ w.toValuationSubring) :
    ∃ c ∈ w.toValuationSubring, D K F g = c • w.dCoord := by
  obtain ⟨u, hu0, hu, hDu⟩ : ∃ u : F, u ≠ 0 ∧ w.ord u = 0 ∧ D K F u = D K F g := by
    rcases eq_or_ne g 0 with rfl | hg0
    · exact ⟨1, one_ne_zero, w.ord_one, by rw [map_zero]; exact Derivation.map_one_eq_zero _⟩
    rcases (ord_nonneg_of_mem w hg).eq_or_lt with h0 | hpos
    · exact ⟨g, hg0, h0.symm, rfl⟩
    · have hne : (1 : F) + g ≠ 0 := by
        intro h
        have : g = -1 := by linear_combination h
        rw [this, ord_neg_one] at hpos
        exact lt_irrefl _ hpos
      refine ⟨1 + g, hne, ?_, ?_⟩
      · rw [AlgebraicCurve.Place.ord_add_eq_of_lt w one_ne_zero hg0
          (by rw [w.ord_one]; exact hpos), w.ord_one]
      · rw [map_add, Derivation.map_one_eq_zero, zero_add]
  rcases AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver w u hu0 hu with hc | hc
  · refine ⟨0, w.toValuationSubring.zero_mem, ?_⟩
    rw [← hDu, ← w.differentialCoeff_smul_dCoord (D K F u), hc]
  · exact ⟨_, mem_of_ord_nonneg w hc, by rw [← hDu, w.differentialCoeff_smul_dCoord]⟩

end PBRegSol

open PBRegSol in
theorem _root_.AlgebraicCurve.pullbackAlong_mem_regularDifferentials_of_isIntegral
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [PerfectField K] [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F']
      [Algebra.EssFiniteType K F']
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [∀ w : AlgebraicCurve.Place K F',
      w.DCoordGenerates]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {ω : Ω[F⁄K]} (hω : ω ∈ AlgebraicCurve.regularDifferentials K F) :
    AlgebraicCurve.Differential.pullbackAlong φ ω ∈ AlgebraicCurve.regularDifferentials K F' := by
  rw [mem_regularDifferentials_iff] at hω ⊢
  intro w
  set v := w.restrictAlong φ hφ with hv
  obtain ⟨f, hf, hωf⟩ := hω v
  obtain ⟨t, ht1, hdt⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have memφ : ∀ x : F, x ∈ v.toValuationSubring → φ x ∈ w.toValuationSubring := fun x hx => by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [map_zero]; exact w.toValuationSubring.zero_mem
    · apply mem_of_ord_nonneg
      rw [AlgebraicCurve.Place.ord_restrictAlong φ hφ w x, ← hv]
      exact mul_nonneg (Int.natCast_nonneg _) (ord_nonneg_of_mem v hx)
  have ht : t ∈ v.toValuationSubring := mem_of_ord_nonneg v (by rw [ht1]; exact zero_le_one)
  obtain ⟨c, hc, hDc⟩ := exists_D_eq_smul_dCoord w (memφ t ht)
  refine ⟨φ f * c, mul_mem (memφ f hf) hc, ?_⟩
  rw [hωf, pullbackAlong_smul, hdt, pullbackAlong_D, hDc, mul_smul]
end AlgebraicCurves.Differentials.Proofs.PullbackAlong_mem_regularDifferentials_of_isIntegral
end ProofImplementation

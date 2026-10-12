/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Differentials.Exists_dlog_of_cartierOperator_fixed
import Nyll.AlgebraicCurves.Differentials.IsRegularDiff_dlog_of_dvd_ord
import Nyll.AlgebraicCurves.Differentials.Dvd_ord_of_isRegularDiff_dlog
import Nyll.AlgebraicCurves.Divisors.Divisor_exists_degZero_ord_eq_mul_of_dvd_ord
import Nyll.JacobianVarieties.Pic0.Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion

/-!
The image of the torsion logarithmic differential map is the space of regular Cartier-fixed
forms.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff
attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

universe u v

open KaehlerDifferential AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.range_eq_setOf_cartier_fixed_and_isRegularDiff
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (δ : Pic0.torsion K F p →+ Ω[F⁄K])
    (hδ : ∀ (y : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
        Pic0.mk E = (y : Pic0 K F) → g ≠ 0 →
        (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) →
        δ y = g⁻¹ • D K F g) :
    Set.range δ = {ω : Ω[F⁄K] | C ω = ω ∧ AlgebraicCurve.IsRegularDiff K F ω} := by
  have hp : p.Prime := Fact.out
  have hClog : ∀ g : F, g ≠ 0 → C (g⁻¹ • D K F g) = g⁻¹ • D K F g := by
    intro g hg
    have hscal : (g⁻¹) ^ p * g ^ (p - 1) = g⁻¹ := by
      have hpow : g ^ p = g ^ (p - 1) * g := (pow_sub_one_mul hp.ne_zero g).symm
      rw [inv_pow, hpow, mul_inv, mul_comm (g ^ (p - 1))⁻¹ g⁻¹, mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ hg), mul_one]
    have h1 : g⁻¹ • D K F g = (g⁻¹) ^ p • (g ^ (p - 1) • D K F g) := by
      rw [smul_smul, hscal]
    conv_lhs => rw [h1]
    rw [hsemi, hlog]
  ext ω
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨E, g, hE, hg, hdvd, hord⟩ :=
      AlgebraicCurve.Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (K := K) (F := F) (n := p) y.2
    have hrec : δ y = g⁻¹ • D K F g := hδ y E g hE hg (fun v => (hord v).symm)
    rw [hrec]
    exact ⟨hClog g hg, AlgebraicCurve.isRegularDiff_dlog_of_dvd_ord p x hdvd⟩
  · rintro ⟨hfix, hreg⟩
    obtain ⟨h, hh, rfl⟩ :=
      AlgebraicCurve.exists_dlog_of_cartierOperator_fixed p x C hsemi hker hlog ω hfix
    have hdvd : ∀ v : Place K F, (p : ℤ) ∣ v.ord h :=
      AlgebraicCurve.dvd_ord_of_isRegularDiff_dlog p x hreg
    obtain ⟨E, hE⟩ :=
      AlgebraicCurve.Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
        (K := K) (F := F) hp.ne_zero hh hdvd
    have htors : Pic0.mk E ∈ Pic0.torsion K F p := by
      rw [Pic0.mem_torsion, Pic0.mk, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf]
      exact ⟨h, hh, fun v => by
        change (p : ℤ) * (E : Divisor K F) v = v.ord h
        exact (hE v).symm⟩
    refine ⟨⟨Pic0.mk E, htors⟩, ?_⟩
    exact hδ _ E h rfl hh (fun v => (hE v).symm)
end JacobianVarieties.Pic0.Proofs.Pic0_range_eq_setOf_cartier_fixed_and_isRegularDiff
end ProofImplementation

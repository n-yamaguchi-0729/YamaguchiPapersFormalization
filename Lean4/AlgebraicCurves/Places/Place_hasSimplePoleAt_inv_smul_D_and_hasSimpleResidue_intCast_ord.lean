/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.Polar
import AlgebraicCurves.Places.Place_hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord

/-!
# Place has Simple Pole At inv smul D and has Simple Residue int Cast ord
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
theorem AlgebraicCurve.Place.isRegularAt_of_hasSimpleResidue_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {ω : Ω[F⁄K]}
    (h : v.HasSimpleResidue ω 0) : v.IsRegularAt ω := by
  obtain ⟨f, rfl, hmem, hres⟩ := h
  refine ⟨f, ?_, rfl⟩
  have hmax : (⟨v.uniformizer * f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal
    v.toValuationSubring := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← IsLocalRing.residue, ]
    change IsLocalRing.residue v.toValuationSubring ⟨v.uniformizer * f, hmem⟩ = 0
    rw [map_zero] at hres
    exact hres
  have hirr := v.irreducible_mk_uniformizer
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr, Ideal.mem_span_singleton]
    at hmax
  obtain ⟨g, hg⟩ := hmax
  have hπ0 : v.uniformizer ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    exact Subtype.ext h0
  have : f = (g : F) := by
    have h' : v.uniformizer * f = v.uniformizer * (g : F) := by
      have := congrArg (Subtype.val) hg
      simpa using this
    exact mul_left_cancel₀ hπ0 h'
  rw [this]
  exact g.2

theorem _root_.AlgebraicCurve.Place.hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (f : F) (hf : f ≠ 0) (v : Place K F) :
    v.HasSimplePoleAt (f⁻¹ • KaehlerDifferential.D K F f) ∧
      v.HasSimpleResidue (f⁻¹ • KaehlerDifferential.D K F f) ((v.ord f : ℤ) : K) := by
  obtain ⟨hp, hr⟩ := Place.hasPoleOrderLE_one_inv_smul_D_and_hasLogResidue_intCast_ord f hf v
  refine ⟨?_, hr⟩
  simp only [Place.HasPoleOrderLE, pow_one] at hp
  exact hp
end AlgebraicCurves.Places.Proofs.Place_hasSimplePoleAt_inv_smul_D_and_hasSimpleResidue_intCast_ord
end ProofImplementation

attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

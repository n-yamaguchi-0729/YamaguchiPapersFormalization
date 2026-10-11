/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_forall_mem_hasValue.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Value
import Nyll.AlgebraicCurves.Places.Place_exists_forall_adicValuation_sub_eq
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Place exists forall mem has Value
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_forall_mem_hasValue
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
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
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_forall_mem_hasValue
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (E : Finset (Place K F)) (c : Place K F → Kˣ) :
    ∃ g : F, ∀ e ∈ E, e.HasValue g (c e) := by
  obtain ⟨g, hg⟩ := AlgebraicCurve.Place.exists_forall_adicValuation_sub_eq E
    (fun e => algebraMap K F (c e : K)) (fun _ => -1)
  refine ⟨g, fun e he => ?_⟩
  have hlt : e.adicValuation (g - algebraMap K F (c e : K)) < 1 := by
    rw [hg e he, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hdmem : g - algebraMap K F (c e : K) ∈ e.toValuationSubring :=
    (e.mem_iff_adicValuation_le_one).mpr hlt.le
  have hgmem : g ∈ e.toValuationSubring := by
    have h := add_mem hdmem (e.algebraMap_mem' (c e : K))
    rwa [sub_add_cancel] at h
  refine ⟨hgmem, ?_⟩
  have hmax : (⟨g - algebraMap K F (c e : K), hdmem⟩ : e.toValuationSubring) ∈
      IsLocalRing.maximalIdeal e.toValuationSubring :=
    (e.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
  have hsplit : (⟨g, hgmem⟩ : e.toValuationSubring) =
      ⟨g - algebraMap K F (c e : K), hdmem⟩ + algebraMap K e.toValuationSubring (c e : K) := by
    apply Subtype.ext
    change g = (g - algebraMap K F (c e : K)) + (algebraMap K e.toValuationSubring (c e : K) : F)
    rw [Place.coe_algebraMap, sub_add_cancel]
  rw [hsplit, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
  exact e.residue_algebraMap (c e : K)

end AlgebraicCurves.Places.Proofs.Place_exists_forall_mem_hasValue
end ProofImplementation

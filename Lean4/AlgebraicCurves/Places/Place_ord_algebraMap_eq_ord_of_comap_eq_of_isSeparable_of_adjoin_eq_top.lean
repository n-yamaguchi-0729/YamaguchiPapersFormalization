/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Divisors.ConstantExtension
import AlgebraicCurves.Places.Place_ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top

/-!
# Place ord algebra Map eq ord of comap eq of is Separable of adjoin eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top

open AlgebraicCurve

theorem
  _root_.AlgebraicCurve.Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
    {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
    [Algebra k k'] [Algebra k F] [Algebra F F'] [Algebra k' F'] [Algebra k F']
    [IsScalarTower k k' F'] [IsScalarTower k F F']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k']
    (hgen : Algebra.adjoin F (Set.range (algebraMap k' F')) = ⊤)
    (x : Place k F) (x' : Place k' F')
    (hx : x'.toValuationSubring.comap (algebraMap F F') = x.toValuationSubring) :
    ∀ f : F, x'.ord (algebraMap F F' f) = x.ord f := by
  have : Algebra.IsIntegral F F' := by
    refine ⟨fun y => ?_⟩
    have hle : Algebra.adjoin F (Set.range (algebraMap k' F')) ≤ integralClosure F F' := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨c, rfl⟩
      have hc : IsIntegral k c := Algebra.IsIntegral.isIntegral c
      exact (hc.map (IsScalarTower.toAlgHom k k' F')).tower_top
    have hy : y ∈ Algebra.adjoin F (Set.range (algebraMap k' F')) := by
      rw [hgen]
      exact Algebra.mem_top
    exact hle hy
  intro f
  have e1 := AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
    (K := k) hgen x'
  have hrestr : (x'.forgetConstants (K := k)).restrict F = x := Place.ext (by
    rw [Place.restrict_toValuationSubring, Place.forgetConstants_toValuationSubring, hx])
  have h := (x'.forgetConstants (K := k)).ord_restrict (F := F) f
  rw [Place.ord_forgetConstants, e1, hrestr, Nat.cast_one, one_mul] at h
  exact h
end Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
end AlgebraicCurves.Places.Proofs
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
attribute [-simp] AlgebraicCurve.Pic.baseChange_mk
  AlgebraicCurve.Place.forgetConstants_toValuationSubring
  AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants
  AlgebraicCurve.Place.extendConstants_toValuationSubring
  AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring
  AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

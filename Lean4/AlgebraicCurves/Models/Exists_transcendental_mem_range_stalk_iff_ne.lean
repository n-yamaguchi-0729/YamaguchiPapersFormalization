/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import AlgebraicCurves.Places.Exists_place_range_stalk_eq
import AlgebraicCurves.Models.Eq_of_range_stalk_eq
import AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import AlgebraicCurves.FunctionFields.ConstantsAreBase_of_deg_eq_one
import AlgebraicCurves.Places.Place_exists_not_mem_and_forall_ne_mem

/-!
# Exists transcendental mem range stalk iff ne

Distinct points of a proper smooth integral curve are separated by a transcendental function in
one local ring and outside the other.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.Exists_transcendental_mem_range_stalk_iff_ne
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

theorem _root_.AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne
    {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (Q : C) (hQ : IsClosed ({Q} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ f : C.functionField, Transcendental K f ∧
      ∀ x : C, f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range ↔ x ≠ Q := by
  let hKF : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have : IsCurveOver K C.functionField :=
    AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  have := SmoothOfRelativeDimension.smooth 1 c
  have : LocallyOfFiniteType c := inferInstance
  have : Algebra.EssFiniteType K C.functionField := AlgebraicCurve.essFiniteType_functionField c
  obtain ⟨vQ, hvQ⟩ := AlgebraicCurve.exists_place_range_stalk_eq c Q hQ
  have hC : ConstantsAreBase K C.functionField :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one vQ (IsCurveOver.deg_eq_one_of_isAlgClosed vQ)
  obtain ⟨f, hfQ, hfw⟩ := AlgebraicCurve.Place.exists_not_mem_and_forall_ne_mem hC vQ
  refine ⟨f, ?_, ?_⟩
  · intro halg
    apply hfQ
    obtain ⟨a, ha⟩ := minpoly.mem_range_of_degree_eq_one K f
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral))
    rw [← ha]
    exact vQ.algebraMap_mem' a
  · intro x
    constructor
    · rintro hx rfl
      rw [hvQ] at hx
      exact hfQ hx
    · intro hx
      by_cases hxc : IsClosed ({x} : Set C)
      · obtain ⟨vx, hvx⟩ := AlgebraicCurve.exists_place_range_stalk_eq c x hxc
        have hne : vx ≠ vQ := by
          intro h
          exact hx (AlgebraicCurve.eq_of_range_stalk_eq c x Q (by rw [hvx, hvQ, h]))
        change f ∈ (algebraMap (C.presheaf.stalk x) C.functionField).range
        rw [hvx]
        exact hfw vx hne
      · have hxg : x = genericPoint C := by
          by_contra h
          exact hxc (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x h)
        subst hxg
        refine ⟨f, ?_⟩
        change (C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint C))).hom f = f
        have : C.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint C)) = 𝟙 _ :=
          TopCat.Presheaf.stalkSpecializes_refl _ _
        rw [this]
        rfl
end AlgebraicCurves.Models.Proofs.Exists_transcendental_mem_range_stalk_iff_ne
end ProofImplementation

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler
attribute [-instance] AlgebraicCurve.IsCurveOver.instFreeKaehler
attribute [-instance] AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
attribute [-instance] AlgebraicCurve.IsCurveOver.instFiniteResidue
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.congrEquiv_apply
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

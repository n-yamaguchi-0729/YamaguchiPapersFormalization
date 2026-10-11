/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Cohomology.RiemannRoch.IndexOfSpecialty_eq_zero_of_genusReached
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Places.Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import AlgebraicCurves.Divisors.Divisor_degree_eq_sum_support
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists

/-!
# Exists index Of Specialty map Domain eq zero of constant Field Extension of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsIndexOfSpecialtyMapDomain
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
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

open AlgebraicCurve

namespace W7XChildE

theorem constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ConstantsAreBase K F := by
  obtain ⟨x, hxt, _⟩ := hfg
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ fun v =>
    Place.adicValuation_algebraMap_le_one v c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hord : ∀ v : Place K F, 0 ≤ v.ord f := fun v => by
    have := (mem_riemannRochSpace_iff.mp hf v).resolve_left hf0; simpa using this
  obtain ⟨Df, hDord, hDdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf0
  have hdiv : ∀ v : Place K F, v.ord f = 0 := by
    by_contra hne; push Not at hne; obtain ⟨v, hv⟩ := hne
    refine absurd hDdeg (ne_of_gt ?_)
    rw [Divisor.degree_eq_sum_support]
    refine Finset.sum_pos' (fun w _ => mul_nonneg (by rw [hDord w]; exact hord w)
      (Int.natCast_nonneg _)) ⟨v, ?_, ?_⟩
    · simp only [Finsupp.mem_support_iff, hDord v]; exact hv
    · rw [hDord v]
      have : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
      have : (v.deg : ℤ) = 1 := by exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite v
      rw [this, mul_one]; exact (hord v).lt_of_ne' hv
  exact ⟨_, (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hxt
    (F := F) hdiv).choose_spec⟩

end W7XChildE

open W7XChildE

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsIndexOfSpecialtyMapDomain

section PublicStatement

open _root_.AlgebraicCurve
open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsIndexOfSpecialtyMapDomain.W7XChildE
open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs.ExistsIndexOfSpecialtyMapDomain

namespace AlgebraicCurve

theorem exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (_hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (_hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (_hlift_inj : Function.Injective lift) :
    ∃ D : Divisor K F, indexOfSpecialty (K := K') (Finsupp.mapDomain lift D) = 0 := by
  classical
  obtain ⟨x, hxt, hxfd⟩ := id hfg
  obtain ⟨x', hxt', hxfd'⟩ := id hfg'
  have : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  have : Algebra.EssFiniteType K' F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt' hxfd'
  have hCAB : ConstantsAreBase K F := constantsAreBase hfg
  have hCAB' : ConstantsAreBase K' F' := constantsAreBase hfg'
  obtain ⟨hne, hfd0, γ, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hCAB
  obtain ⟨hne', hfd0', γ', D₀', hD₀'⟩ :=
    stichtenothGenusExists_of_isCurveOver (K := K') (F := F') hCAB'
  have := hne; have := hfd0; have := hne'; have := hfd0'
  obtain ⟨P₀⟩ := hne
  obtain ⟨n, hRGA⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hD₀' (lift P₀)
  refine ⟨Finsupp.single P₀ (n : ℤ), ?_⟩
  have hmap : (Finsupp.mapDomain lift (Finsupp.single P₀ (n : ℤ)) : Divisor K' F')
      = (n : ℤ) • Finsupp.single (lift P₀) (1 : ℤ) := by
    rw [Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hmap]
  exact indexOfSpecialty_eq_zero_of_genusReached hRGA

end AlgebraicCurve

end PublicStatement
end ProofImplementation

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

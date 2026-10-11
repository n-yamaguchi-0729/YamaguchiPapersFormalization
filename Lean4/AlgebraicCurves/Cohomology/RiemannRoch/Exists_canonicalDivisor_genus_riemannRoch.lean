/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Cohomology.RiemannRoch
import AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.FunctionFields.InstIsCurveOverRatFunc
import AlgebraicCurves.FunctionFields.FunctionField_exists_ratFuncAlgHom_apply_X_eq

/-!
Existence of a canonical divisor and the Riemann--Roch genus formula over an algebraically closed
field.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Exists_canonicalDivisor_genus_riemannRoch
open _root_.IsDedekindDomain.HeightOneSpectrum
  (instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal)
  in
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt) in
attribute [-instance] AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

universe u v

open IntermediateField Polynomial

namespace S18RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_and_isSeparable_of_ratFuncAlgHom (t : F)
    (hfd : FiniteDimensional K⟮t⟯ F) (hsep : Algebra.IsSeparable K⟮t⟯ F)
    (φ : RatFunc K →ₐ[K] F) (hφ : φ RatFunc.X = t) :
    letI := φ.toRingHom.toAlgebra
    Module.Finite (RatFunc K) F ∧ Algebra.IsSeparable (RatFunc K) F := by
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let E : IntermediateField K F := φ.fieldRange
  have htE : t ∈ E := ⟨RatFunc.X, hφ⟩
  have hle : K⟮t⟯ ≤ E := adjoin_simple_le_iff.mpr htE
  let : Algebra K⟮t⟯ E := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K⟮t⟯ E F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have : Module.Finite E F := Module.Finite.of_restrictScalars_finite K⟮t⟯ E F
  have : Algebra.IsSeparable E F := Algebra.isSeparable_tower_top_of_isSeparable K⟮t⟯ E F
  let e : RatFunc K ≃ₐ[K] E := AlgEquiv.ofInjectiveField φ
  have key : ∀ x : E, φ (e.symm x) = (x : F) := fun x => by
    have h2 : ((e (e.symm x) : E) : F) = φ (e.symm x) := AlgEquiv.ofInjective_apply _ _ _
    rw [e.apply_symm_apply] at h2
    exact h2.symm
  have he : (algebraMap (RatFunc K) F).comp (e.symm.toRingEquiv : E ≃+* RatFunc K).toRingHom
      = (RingEquiv.refl F).toRingHom.comp (algebraMap E F) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact key x
  refine ⟨?_, ?_⟩
  · exact Module.Finite.of_equiv_equiv (e.symm.toRingEquiv : E ≃+* RatFunc K) (RingEquiv.refl F) he
  · exact Algebra.IsSeparable.of_equiv_equiv (e.symm.toRingEquiv : E ≃+* RatFunc K)
      (RingEquiv.refl F) he

theorem essFiniteType_ratFunc (K : Type*) [Field K] : Algebra.EssFiniteType K (RatFunc K) := by
  have : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  exact Algebra.EssFiniteType.comp K K[X] (RatFunc K)

end S18RR

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch (K : Type u) [Field K]
    [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ (Kc : Divisor K F) (g : ℕ), ∀ D : Divisor K F,
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by
  classical
  obtain ⟨t, htr, hfd, hsep⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have ht : t ∉ Set.range (algebraMap K F) := by
    rintro ⟨k, rfl⟩
    exact htr (isAlgebraic_algebraMap k)
  obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq (K := K) (F := F)
    ht
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq (fun k => (φ.commutes k).symm)
  obtain ⟨hfin, hsepR⟩ := S18RR.finite_and_isSeparable_of_ratFuncAlgHom t hfd hsep φ hφ
  have : Module.Finite (RatFunc K) F := hfin
  have : Algebra.IsSeparable (RatFunc K) F := hsepR
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  have : AlgebraicCurve.IsCurveOver K (RatFunc K) := AlgebraicCurve.instIsCurveOverRatFunc K
  have : Algebra.EssFiniteType K (RatFunc K) := S18RR.essFiniteType_ratFunc K
  have : AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  have : ∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have : ∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
  obtain ⟨ω, hω⟩ := exists_ne (0 : KaehlerDifferential K F)
  exact ⟨AlgebraicCurve.canonicalDivisorOf hω, AlgebraicCurve.genus K F, fun D => hRR hω D⟩
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Exists_canonicalDivisor_genus_riemannRoch
end ProofImplementation

attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

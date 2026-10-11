/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Polar
import AlgebraicCurves.Places.Value
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Residues.Canonical
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Differentials.Uniformizer
import AlgebraicCurves.Differentials.Residues.ResidueTheoremK_of_isAlgClosed
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc

/-!
# Sum eq zero of forall has Simple Residue of mem polar Differentials
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs
namespace Sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

noncomputable section

open KaehlerDifferential IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace ResThm

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

theorem residueTheoremK : ResidueTheoremK K F := by
  classical
  have : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨t, ht, hfin, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have := hfin
  have := hsep
  have : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  have : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial K))
  have : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  have : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  let : Algebra (RatFunc K) F := ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    ext y
    change algebraMap K⟮t⟯ F (e (e.symm y)) = algebraMap K⟮t⟯ F y
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have hfd : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _
  exact residueTheoremK_of_isAlgClosed (K := K) (F := F)

variable {K F}

omit [Algebra.EssFiniteType K F] [HasCanonicalDivisor (K := K) (F := F)] in
theorem trace_res_differentialCoeff_of_hasSimpleResidue {v : Place K F} {ω : Ω[F⁄K]} {a : K}
    (h : v.HasSimpleResidue ω a) :
    Algebra.trace K v.ResidueField
        ((HasCanonicalLocalResidueKStar.dataKStar v).res (v.differentialCoeff ω)) = a := by
  obtain ⟨f, hf, hval⟩ := h
  have hdeg : Module.finrank K v.ResidueField = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed v
  rw [v.differentialCoeff_unique hf, (HasCanonicalLocalResidueKStar.dataKStar v).res_simplePole f
    hval.mem,
    hval.residue_eq, Algebra.trace_algebraMap, hdeg, one_smul]
omit [Algebra.EssFiniteType K F] [HasCanonicalDivisor (K := K) (F := F)] in
theorem res_differentialCoeff_eq_zero_of_isRegularAt {v : Place K F} {ω : Ω[F⁄K]}
    (h : v.IsRegularAt ω) :
    (HasCanonicalLocalResidueKStar.dataKStar v).res (v.differentialCoeff ω) = 0 := by
  obtain ⟨f, hf, hωf⟩ := h
  rw [v.differentialCoeff_unique hωf]
  exact (HasCanonicalLocalResidueKStar.dataKStar v).res_of_mem f hf
omit [Algebra.EssFiniteType K F] [HasCanonicalDivisor (K := K) (F := F)] in
theorem eq_zero_of_hasSimpleResidue_zero {v : Place K F} {a : K} (h : v.HasSimpleResidue (0 :
  Ω[F⁄K]) a) :
    a = 0 := by
  have ht := trace_res_differentialCoeff_of_hasSimpleResidue h
  rw [v.differentialCoeff_zero, map_zero, map_zero] at ht
  exact ht.symm

theorem main (S : Finset (Place K F)) (ω : Ω[F⁄K])
    (hω : ω ∈ polarDifferentials K F (S : Set (Place K F)))
    (a : Place K F → K) (ha : ∀ v ∈ S, v.HasSimpleResidue ω (a v)) :
    ∑ v ∈ S, a v = 0 := by
  classical
  rcases eq_or_ne ω 0 with rfl | hω0
  · exact Finset.sum_eq_zero fun v hv => eq_zero_of_hasSimpleResidue_zero (ha v hv)
  · have hRT := residueTheoremK K F
    have h := hRT HasCanonicalLocalResidueKStar.dataKStar hω0 1
    rw [weilOfKaehlerK_apply] at h
    have hterm : ∀ v : Place K F,
        kaehlerResidueTermKFam HasCanonicalLocalResidueKStar.dataKStar ω
          ((⟨diagonalHom K F 1, diagonal_mem_adeleSpace 1⟩ : adeleSpace K F) : Place K F → F) v =
        if v ∈ S then a v else 0 := by
      intro v
      rw [kaehlerResidueTermKFam_apply]
      rw [show ((⟨diagonalHom K F 1, diagonal_mem_adeleSpace 1⟩ : adeleSpace K F) : Place K F → F)
        v = 1
        from rfl, one_mul]
      split_ifs with hv
      · exact trace_res_differentialCoeff_of_hasSimpleResidue (ha v hv)
      · rw [res_differentialCoeff_eq_zero_of_isRegularAt ((hω v).1
          (by exact_mod_cast hv)), map_zero]
    rw [finsum_congr hterm] at h
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?_] at h
    · rw [← h]
      exact Finset.sum_congr rfl fun v hv => by rw [ite_eq_left hv]
    · intro v hv
      rw [Function.mem_support] at hv
      by_contra hvS
      exact hv (ite_eq_right (by exact_mod_cast hvS))

end ResThm

end AlgebraicCurve

end

theorem _root_.AlgebraicCurve.sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (ω : Ω[F⁄K])
    (hω : ω ∈ AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F)))
    (a : AlgebraicCurve.Place K F → K) (ha : ∀ v ∈ S, v.HasSimpleResidue ω (a v)) :
    ∑ v ∈ S, a v = 0 := by
  have : PerfectField K := IsAlgClosed.perfectField K
  have : ∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  exact AlgebraicCurve.ResThm.main S ω hω a ha

end Sum_eq_zero_of_forall_hasSimpleResidue_of_mem_polarDifferentials
end AlgebraicCurves.Differentials.Residues.Proofs
end ProofImplementation

open _root_.IsDedekindDomain.HeightOneSpectrum in
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single
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

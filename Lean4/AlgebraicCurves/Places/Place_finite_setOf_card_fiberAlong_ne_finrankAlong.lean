/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_finite_setOf_card_fiberAlong_ne_finrankAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Places.Exists_finset_forall_not_mem_ramificationIndex_eq_one
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver
import AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import AlgebraicCurves.Places.Place_exists_ord_neg_of_transcendental
import AlgebraicCurves.FunctionFields.IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import AlgebraicCurves.Places.Place_kaehlerD_ne_zero_of_ord_eq_one
import AlgebraicCurves.Places.Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
import AlgebraicCurves.Places.Place_card_fiberAlong_le_finrankAlong_and_iff

/-!
# Place finite set Of card fiber Along ne finrank Along
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_finite_setOf_card_fiberAlong_ne_finrankAlong
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
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
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
attribute [-simp] AlgebraicCurve.kaehlerResidueTermKFam_apply
  AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

open AlgebraicCurve IntermediateField

namespace B13L3b

theorem exists_D_sub_algebraMap_ne_zero {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field L] [Algebra K L] [IsCurveOver K L] [Algebra.EssFiniteType K L]
    {s : L} (hs : Transcendental K s) :
    ∃ c : K, KaehlerDifferential.D K L (s - algebraMap K L c) ≠ 0 := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hfd : FiniteDimensional K⟮s⟯ L :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hs
  have := hfd
  have : Algebra.IsAlgebraic K⟮s⟯ L := Algebra.IsAlgebraic.of_finite K⟮s⟯ L
  have : Algebra.IsIntegral K⟮s⟯ L := Algebra.IsIntegral.of_finite K⟮s⟯ L
  have : CharZero K⟮s⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮s⟯).injective
  have hsep : Algebra.IsSeparable K⟮s⟯ L := Algebra.IsSeparable.of_integral K⟮s⟯ L
  obtain ⟨C, hC⟩ :=
    AlgebraicCurve.Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos s hs hfd hsep
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset C
  refine ⟨c, ?_⟩
  set u : L := s - algebraMap K L c with hu
  have hu_tr : Transcendental K u := by
    intro halg
    apply hs
    have h' : IsAlgebraic K (u + algebraMap K L c) := halg.add (isAlgebraic_algebraMap c)
    simpa [hu] using h'
  have huinv_tr : Transcendental K u⁻¹ := fun h => hu_tr (IsAlgebraic.inv_iff.1 h)
  have : FiniteDimensional K⟮u⁻¹⟯ L :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType huinv_tr
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental u⁻¹ huinv_tr
  have hpos : 0 < w.ord u := by
    rw [w.ord_inv] at hw
    omega
  have hone : w.ord u = 1 := hC c hc w hpos
  exact AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one s w hone

end B13L3b

open B13L3b

theorem _root_.AlgebraicCurve.Place.finite_setOf_card_fiberAlong_ne_finrankAlong
    {K F F' : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Field F'] [Algebra K F]
      [Algebra K F']
    [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) :
    {P : Place K F | (Place.fiberAlong φ hφ P).card ≠ finrankAlong K φ}.Finite := by
  classical
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : Module.Finite F F' := hfin
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  have hsepI : Algebra.IsSeparable F F' := Algebra.IsSeparable.of_integral F F'
  have hsep : SeparableAlong K φ := hsepI
  have : ∀ v : Place K F, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have : ∀ w : Place K F', w.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have : HasCanonicalDivisor (K := K) (F := F) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  have : HasCanonicalDivisor (K := K) (F := F') := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  have hreg := AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver (K := K) (F' := F')
  have htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w =>
    Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 (w.ramificationIndex_pos (F := F)))
  obtain ⟨t, ht, -, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F
    := F)
  have hφt : Transcendental K (φ t) := by
    have h := (transcendental_algebraMap_iff (A := F') (algebraMap F F').injective).2 ht
    exact h
  obtain ⟨c, hc⟩ := exists_D_sub_algebraMap_ne_zero (K := K) (L := F') hφt
  set u : F := t - algebraMap K F c with hu
  have hω₀' : KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F u) ≠ 0 := by
    rw [KaehlerDifferential.map_D]
    have hmap : algebraMap F F' u = φ t - algebraMap K F' c := by
      change φ u = _
      rw [hu, map_sub, AlgHom.commutes]
    rw [hmap]
    exact hc
  have hω₀ : KaehlerDifferential.D K F u ≠ 0 := by
    intro h
    apply hω₀'
    rw [h, map_zero]
  obtain ⟨S, hS⟩ := AlgebraicCurve.exists_finset_forall_not_mem_ramificationIndex_eq_one
    (K := K) (F := F) (F' := F') hreg htame hω₀ hω₀'
  refine (S.image (fun w : Place K F' => w.restrictAlong φ hφ)).finite_toSet.subset ?_
  intro P hP
  simp only [Set.mem_ofPred_eq] at hP
  have h3a := AlgebraicCurve.Place.card_fiberAlong_le_finrankAlong_and_iff φ hφ hfin hsep P
  have hex : ∃ W ∈ Place.fiberAlong φ hφ P, W.ramificationIndexAlong φ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hP (h3a.2.2 hcon)
  obtain ⟨W, hW, hWe⟩ := hex
  have hWS : W ∈ S := by
    by_contra hWS
    exact hWe (hS W hWS)
  rw [Finset.coe_image]
  exact ⟨W, hWS, (Place.mem_fiberAlong).1 hW⟩
end AlgebraicCurves.Places.Proofs.Place_finite_setOf_card_fiberAlong_ne_finrankAlong
end ProofImplementation

attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq
  AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply
  AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

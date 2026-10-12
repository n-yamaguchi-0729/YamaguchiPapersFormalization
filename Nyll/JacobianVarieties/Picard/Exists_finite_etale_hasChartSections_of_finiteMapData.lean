/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_finiteMapData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_canonicalDivisor_genus_riemannRoch
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_sections_injective_of_tensorProduct_algEquiv_pi

/-!
# Finite etale chart sections from finite-map data

Split the finite etale algebra after a faithfully flat extension to obtain distinct
sections. Riemann--Roch then selects the sections required by the chart criterion.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FiniteEtaleChartSections
attribute [-instance]
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
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
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
attribute [-instance]
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
attribute [-simp]
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
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
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
attribute [-simp]
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk
attribute [-simp] AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.AlgebraicCurve hiding genus

/-- Split sufficiently large etale level sets and use Riemann--Roch to construct
chart sections after a finite faithfully flat etale extension of a local noetherian base. -/
theorem _root_.AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧
      𝔉.LevelSetsGenericallyEtale) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R')
      (n g r : ℕ) (_ : 2 * g < r)
      (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')),
      HasChartSections (baseChange R c R') γ := by
  classical
  obtain ⟨𝔉₀, -⟩ := h𝔉 0
  obtain ⟨g, hg⟩ := exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData R c ε 𝔉₀
  obtain ⟨R₀, _, _, _, _, _, _, _, B, _, _, _, _, ι, hιci, hι, hN⟩ :=
    exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData R c ε h𝔉 (2 * g + 2)
  obtain ⟨R', _, _, _, _, _, _, ⟨φ⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi R₀ B
  let : Algebra R R' := Algebra.compHom R' (algebraMap R R₀)
  have : IsScalarTower R R₀ R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite R R' := Module.Finite.trans R₀ R'
  have : Algebra.Etale R R' := Algebra.Etale.comp R R₀ R'
  have : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.trans R R₀ R'
  have : IsClosedImmersion ι := hιci
  obtain ⟨σ, hσ⟩ := exists_sections_injective_of_tensorProduct_algEquiv_pi R c R₀ B ι hι R'
    (Module.finrank R₀ B) φ
  let E := Fintype.equivFin (Fin (2 * g + 1 - g) → Fin (Module.finrank R₀ B))
  refine ⟨R', inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    Fintype.card (Fin (2 * g + 1 - g) → Fin (Module.finrank R₀ B)), g, 2 * g + 1, by omega,
    fun i j => σ (E.symm i j), ?_⟩
  intro k _ _ s
  obtain ⟨L, _, _, _, _, M, e, he⟩ :=
    exists_curveModel_iso_pullback_of_isAlgClosed R' (baseChange R c R') k s
  refine ⟨L, inferInstance, inferInstance, M, e, he, ?_⟩
  obtain ⟨Kc, g', hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch k L
  have hgg : g' = g := by
    refine hg k (s ≫ specMap R R') L M
      (e ≪≫ pullbackLeftPullbackSndIso c (specMap R R') s) ?_ Kc g' hRR
    rw [Iso.trans_hom, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, he]
  rw [hgg] at hRR
  refine ⟨⟨Kc, hRR⟩, ?_⟩
  intro D _ hdegD
  let P : {p : Spec (CommRingCat.of k) ⟶ pullback (baseChange R c R') s //
      p ≫ pullback.snd (baseChange R c R') s = 𝟙 _} → Place k L :=
    fun q => M.pointEquivPlace ⟨q.1 ≫ e.inv, by
      rw [Category.assoc, ← he, e.inv_hom_id_assoc]
      exact q.2⟩
  have hPinj : Function.Injective P := by
    intro q q' h
    have h1 := congrArg Subtype.val (M.pointEquivPlace.injective h)
    exact Subtype.ext ((cancel_mono e.inv).mp h1)
  let pl : Fin (Module.finrank R₀ B) → Place k L := fun m => P (sectionFibrePoint (σ m) s)
  have key : ∀ m, (sectionFibrePoint (σ m) s).1 ≫ pullback.fst (baseChange R c R') s =
      s ≫ (σ m).1 :=
    fun m => pullback.lift_fst _ _ _
  have hplinj : Function.Injective pl := by
    intro m m' h
    have h1 := congrArg (fun q => q.1 ≫ pullback.fst (baseChange R c R') s) (hPinj h)
    rw [key, key] at h1
    exact hσ k s h1
  let S : Finset (Place k L) := Finset.univ.image pl
  have hScard : 2 * g + 1 + 1 ≤ S.card := by
    have : S.card = Module.finrank R₀ B := by
      rw [Finset.card_image_of_injective _ hplinj, Finset.card_univ, Fintype.card_fin]
    omega
  have hS1 : ∀ v ∈ S, v.deg = 1 := fun v _ => IsCurveOver.deg_eq_one_of_isAlgClosed v
  obtain ⟨f, -, hfS, hf⟩ :=
    RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card hRR (by omega) S hS1
      hScard D hdegD
  have hch : ∀ j, ∃ m, pl m = f j := fun j => by
    obtain ⟨m, _, hm⟩ := Finset.mem_image.mp (hfS j)
    exact ⟨m, hm⟩
  choose μ hμ using hch
  refine ⟨E μ, ?_⟩
  change ell (D - ∑ j, Finsupp.single (P (sectionFibrePoint (σ (E.symm (E μ) j)) s)) 1) = 1
  simp only [Equiv.symm_apply_apply]
  have hsum : ∑ j, Finsupp.single (P (sectionFibrePoint (σ (μ j)) s)) (1 : ℤ)
      = ∑ j, Finsupp.single (f j) 1 :=
    Finset.sum_congr rfl fun j _ => by rw [← hμ j]
  rw [hsum]
  exact hf
end JacobianVarieties.Picard.Proofs.FiniteEtaleChartSections
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
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
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
attribute [-instance]
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Geometry.Picard.IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_sup_eq_top
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_forall_mem_of_finset
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import Nyll.AlgebraicCurves.Cohomology.Sheaves.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.Models.CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
import Nyll.AlgebraicCurves.Geometry.Schemes.subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I

/-!
# Injective choices of points with vanishing twisted first cohomology

Translate the Riemann--Roch point-selection argument through the curve model and Cartier ideals.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.InjectiveTwistedSections
attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
attribute [-instance]
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
attribute [-simp]
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one
  AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
attribute [-simp]
  AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
attribute [-simp]
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq
  AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply
  AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule
  AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

universe u v w

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicCurve hiding genus
open _root_.AlgebraicCurve
open _root_.Opposite

noncomputable section

namespace AlgebraicCurve

export _root_.AlgebraicCurve (
  CurveModel
  Place
  Divisor
  Divisor.degree
  Divisor.degree_single
  Pic
  ell
  H1
  IsCurveOver
  IsCurveOver.deg_eq_one_of_isAlgClosed
  exists_isAffineOpen_sup_eq_top
  exists_isAffineOpen_forall_mem_of_finset
  isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
  CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
  RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card)

namespace CurveModel

export _root_.AlgebraicCurve.CurveModel (
  pointEquivPlace
  toBase
  C
  ffEquiv
  ffEquiv_algebraMap
  smooth
  finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell)

open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve hiding genus

/-- Transfer the injective Riemann--Roch choice of places to rational points. -/
theorem exists_injective_forall_forall_mem_ell_sum_single_pointEquivPlace_sub_eq_one
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    {F : Type u} [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x = M.toBase)
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    (P : Fin r → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _})
    {ι : Type w} [Fintype ι] (B : ι → Finset {p : Spec (CommRingCat.of K) ⟶ X // p
      ≫ x = 𝟙 _})
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ v : Fin (r - g) → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _}, (∀ j, v j ∈ B (a j)) →
        ell ((∑ m, Finsupp.single (M.pointEquivPlace ⟨(P m).1 ≫ e.inv, by
                rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2⟩) (1 : ℤ)) -
             ∑ j, Finsupp.single (M.pointEquivPlace ⟨(v j).1 ≫ e.inv, by
                rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (v j).2⟩) (1 : ℤ)) = 1 := by
  classical
  let pl : {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _} → Place K F := fun q =>
    M.pointEquivPlace ⟨q.1 ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact q.2⟩
  have hpl : Function.Injective pl := by
    intro q q' h
    have h1 := M.pointEquivPlace.injective h
    have h2 : q.1 ≫ e.inv = q'.1 ≫ e.inv := congrArg Subtype.val h1
    exact Subtype.ext ((cancel_mono e.inv).mp h2)
  let B' : ι → Finset (Place K F) := fun i => (B i).image pl
  have hB' : ∀ i, ∀ w ∈ B' i, w.deg = 1 := fun i w _ => IsCurveOver.deg_eq_one_of_isAlgClosed w
  have hdisj' : ∀ i i', i ≠ i' → Disjoint (B' i) (B' i') := fun i i' hne =>
    Finset.disjoint_image hpl |>.mpr (hdisj i i' hne)
  have hbB' : ∀ i, (B' i).card ≤ b := fun i => by
    rw [Finset.card_image_of_injective _ hpl]; exact hb i
  let D : Fin 1 → Divisor K F := fun _ => ∑ m, Finsupp.single (pl (P m)) (1 : ℤ)
  have hdeg : ∀ k, Divisor.degree (D k) = r := fun _ => by
    change Divisor.degree (∑ m, Finsupp.single (pl (P m)) (1 : ℤ)) = r
    rw [map_sum, Finset.sum_congr rfl fun m _ => by
      rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed (pl (P m)), Nat.cast_one,
        mul_one]]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hcard' : 1 * r * b ^ (r - g) + (r - g) < Fintype.card ι := by rwa [one_mul]
  obtain ⟨a, ha, h⟩ :=
    AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
      hRR hgr D hdeg B' hB' hdisj' hb1 hbB' hcard'
  refine ⟨a, ha, fun v hv => ?_⟩
  exact h 0 (fun j => pl (v j)) (fun j => Finset.mem_image_of_mem pl (hv j))

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Hom.ker_comp_of_isIso
  Scheme.IdealSheafData.ideal_mul
  Scheme.Modules.Hom.zero_app
  SmoothOfRelativeDimension
  IsProper
  Scheme.Modules.pullback
  Scheme.Hom
  Scheme.Modules.presheaf
  GeometricallyIrreducible
  Scheme.Modules.Hom
  Spec
  IsIntegral
  Scheme
  Scheme.Modules.Hom.app
  Scheme.IdealSheafData.comap_top
  Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
  IsClosedImmersion
  IsSeparated
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackId
  Scheme.Modules
  Scheme.IdealSheafData.ext
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover
  RelEffCartierDiv
  Scheme.IdealSheafData.IsInvertible
  Scheme.IdealSheafData.isInvertible_top
  graphOver
  prodKerGraph
  prodKerGraph_eq_prod
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0
  RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
  RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
  Scheme.Hom.isInvertible_ker_of_comp_eq_id
  subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
  GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed
  Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso)

namespace WrapB

open _root_.AlgebraicGeometry

/-- A two-affine cover is determined by its two open subsets. -/
theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

/-- The compatible section family obtained by restricting a global section. -/
def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     change (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top :
       U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

/-- The restricted section family recovers its original global section. -/
theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  change (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

/-- A nonzero global section gives a nonzero morphism from the unit module. -/
theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ
    :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

/-- Nontrivial zeroth cohomology gives a nonzero section morphism. -/
theorem exists_section_ne_zero {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K))
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (h : Nontrivial (𝒱.sectionsOf x M).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱.sectionsOf x M).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  exact exists_hom_ne_zero M (eΓ.symm y) hσ

end AlgebraicGeometry.WrapB

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (
  Scheme.Hom.ker_comp_of_isIso
  Scheme.IdealSheafData.ideal_mul
  Scheme.Modules.Hom.zero_app
  SmoothOfRelativeDimension
  IsProper
  Scheme.Modules.pullback
  Scheme.Hom
  Scheme.Modules.presheaf
  GeometricallyIrreducible
  Scheme.Modules.Hom
  Spec
  IsIntegral
  Scheme
  Scheme.Modules.Hom.app
  Scheme.IdealSheafData.comap_top
  Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
  IsClosedImmersion
  IsSeparated
  Scheme.Modules.pullbackCongr
  Scheme.Modules.pullbackId
  Scheme.Modules
  Scheme.IdealSheafData.ext
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  Scheme.TwoAffineOpenCover
  RelEffCartierDiv
  Scheme.IdealSheafData.IsInvertible
  Scheme.IdealSheafData.isInvertible_top
  graphOver
  prodKerGraph
  prodKerGraph_eq_prod
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0
  RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
  RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
  Scheme.Hom.isInvertible_ker_of_comp_eq_id
  subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
  GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed
  Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (
  Hom.ker_comp_of_isIso
  IdealSheafData.ideal_mul
  Modules.Hom.zero_app
  Modules.pullback
  Hom
  Modules.presheaf
  Γ
  empty
  Hom.app
  Modules.Hom
  Modules.Hom.app
  IdealSheafData.comap_top
  IdealSheafData.ker_fst_of_isClosedImmersion
  Modules.pullbackCongr
  Modules.pullbackId
  Modules
  Opens
  IdealSheafData.ext
  IdealSheafData
  Modules.pullbackComp
  IdealSheafData.ideal_comap_of_isOpenImmersion
  Modules.IsInvertible
  Modules.pullbackUnitIso
  TwoAffineOpenCover
  IdealSheafData.IsInvertible
  IdealSheafData.isInvertible_top
  TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0
  TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
  Hom.isInvertible_ker_of_comp_eq_id
  IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (
  Hom.zero_app
  pullback
  presheaf
  Hom
  Hom.app
  pullbackCongr
  pullbackId
  pullbackComp
  IsInvertible
  pullbackUnitIso
  tensor)
namespace IsInvertible
export _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible (pullback tensor)
end AlgebraicGeometry.Scheme.Modules.IsInvertible

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

open scoped _root_.AlgebraicGeometry in
open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Modules in
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
open AlgebraicGeometry.WrapB in
/-- An effective Cartier divisor presents the pulled-back invertible module. -/
theorem exists_nonempty_pullback_fst_iso_invModule_prodKerGraph_of_eulerChar_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) (r : ℕ)
    (h0 : 0 < Module.finrank K (𝒱.sectionsOf x M).H0)
    (hχ : (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
      (Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 + r) :
    ∃ (Pt : Fin r → (Spec (CommRingCat.of K) ⟶ X)) (hPt : ∀ m, Pt m ≫ x = 𝟙 _),
      (prodKerGraph x Pt hPt).IsInvertible ∧
      Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst x (𝟙 (Spec (CommRingCat.of K))))).obj
        M ≅
        (prodKerGraph x Pt hPt).invModule) := by
  have : GeometricallyIrreducible x := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed x
  let φ : Limits.pullback x (𝟙 (Spec (CommRingCat.of K))) ≅ X := asIso (Limits.pullback.fst x (𝟙 _))
  have hφ : φ.hom ≫ x = Limits.pullback.snd x (𝟙 _) := by
    change Limits.pullback.fst x (𝟙 _) ≫ x = _
    rw [Limits.pullback.condition, Category.comp_id]
  let MY : (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules := (Scheme.Modules.pullback
    φ.hom).obj M
  have hMY : Scheme.Modules.IsInvertible MY := hM.pullback φ.hom
  obtain ⟨𝒱Y, hU0, hU1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (Limits.pullback.snd x (𝟙 _)) x φ hφ 𝒱 M MY (Iso.refl _)
  obtain ⟨𝒱Y', hU0', hU1', ⟨u0⟩, ⟨u1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (Limits.pullback.snd x (𝟙 _)) x φ hφ 𝒱 (𝟙_ X.Modules) (𝟙_ (Limits.pullback x (𝟙 (Spec
      (CommRingCat.of K)))).Modules)
    (Scheme.Modules.pullbackUnitIso φ.hom).symm
  obtain rfl : 𝒱Y' = 𝒱Y := cover_ext (hU0'.trans hU0.symm) (hU1'.trans hU1.symm)
  have hnt : Nontrivial (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _)) MY).H0 :=
    Module.nontrivial_of_finrank_pos (R := K) (by rw [e0.finrank_eq]; exact h0)
  obtain ⟨sY, hsY⟩ := exists_section_ne_zero (Limits.pullback.snd x (𝟙 _)) 𝒱Y' MY hnt
  have hχY : (Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _)) MY).H0 : ℤ) -
      Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _)) MY).H1 =
      (Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _))
          (𝟙_ (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules)).H0 : ℤ) -
        Module.finrank K (𝒱Y'.sectionsOf (Limits.pullback.snd x (𝟙 _))
          (𝟙_ (Limits.pullback x (𝟙 (Spec (CommRingCat.of K)))).Modules)).H1 + r := by
    rw [e0.finrank_eq, e1.finrank_eq, u0.finrank_eq, u1.finrank_eq]; exact hχ
  obtain ⟨D, -, ⟨eD, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := x)
    (𝟙 _) hMY sY hsY 𝒱Y' r hχY
  obtain ⟨Pt, hPt, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D
  refine ⟨Pt, hPt, hDI ▸ D.isInvertible_I, ⟨eD ≪≫ eqToIso ?_⟩⟩
  change D.I.invModule = _
  rw [hDI]

end AlgebraicGeometry.Scheme.Modules.IsInvertible

namespace WSM

/-- A finite product of invertible ideal sheaves is invertible. -/
theorem isInvertible_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top] using
      Scheme.IdealSheafData.isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Pullback along an isomorphism preserves products of ideal sheaves. -/
theorem comap_mul_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] (I J : X.IdealSheafData) :
    (I * J).comap φ = I.comap φ * J.comap φ := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply]
  set e : Γ(Y, U) ≃+* Γ(X, φ ''ᵁ U) := (φ.appIso U).symm.commRingCatIsoToRingEquiv with he
  have hinv : (φ.appIso U).inv.hom = e.toRingHom := rfl
  rw [hinv]
  change Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _ =
    Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _ * Ideal.comap (e : Γ(Y, U) →+* Γ(X, φ ''ᵁ U)) _
  rw [Ideal.comap_coe, Ideal.comap_coe, Ideal.comap_coe, ← Ideal.map_symm, ← Ideal.map_symm, ←
    Ideal.map_symm,
    Ideal.map_mul]

/-- Pullback along an isomorphism preserves finite products of ideal sheaves. -/
theorem comap_prod_of_isIso {X Y : Scheme.{u}} (φ : Y ⟶ X) [IsIso φ] {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) : (∏ i ∈ s, I i).comap φ = ∏ i ∈ s, (I i).comap φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul_of_isIso, ih]

/-- The graph ideal is the pullback of the corresponding point ideal. -/
theorem ker_graphOver_eq_comap {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsSeparated x]
    (q : Spec (CommRingCat.of K) ⟶ X) (hq : q ≫ x = 𝟙 _) :
    (graphOver x q hq).ker = q.ker.comap (pullback.fst x (𝟙 (Spec (CommRingCat.of K)))) := by
  have : IsClosedImmersion (q ≫ x) := by rw [hq]; infer_instance
  have : IsClosedImmersion q := .of_comp q x
  set φ := pullback.fst x (𝟙 (Spec (CommRingCat.of K))) with hφ
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion q φ]
  let l : Spec (CommRingCat.of K) ⟶ pullback φ q := pullback.lift (graphOver x q hq) (𝟙 _)
    (by simp only [hφ, graphOver_fst, Category.id_comp])
  have hl : l ≫ pullback.snd φ q = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsIso l := IsIso.of_isIso_fac_right hl
  have hgl : graphOver x q hq = l ≫ pullback.fst φ q := (pullback.lift_fst _ _ _).symm
  rw [hgl, Scheme.Hom.ker_comp_of_isIso]

/-- The product of graph ideals is the pullback of the product of point ideals. -/
theorem prodKerGraph_eq_comap {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsSeparated x]
    {r : ℕ} (Pt : Fin r → (Spec (CommRingCat.of K) ⟶ X)) (hPt : ∀ m, Pt m ≫ x = 𝟙 _) :
    prodKerGraph x Pt hPt = (∏ m, (Pt m).ker).comap (pullback.fst x (𝟙 (Spec (CommRingCat.of K))))
      := by
  rw [prodKerGraph_eq_prod, comap_prod_of_isIso]
  exact Finset.prod_congr rfl fun m _ => ker_graphOver_eq_comap x (Pt m) (hPt m)

private def _root_.WSM.pullbackUnitIso {X Y : Scheme.{u}} (φ : Y ≅ X) (N : X.Modules) :
    N ≅ (Scheme.Modules.pullback φ.inv).obj ((Scheme.Modules.pullback φ.hom).obj N) :=
  ((Scheme.Modules.pullbackId X).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm

export _root_.WSM (pullbackUnitIso)

/-- Recover a module isomorphism from its pullback along a scheme isomorphism. -/
def isoOfPullbackIso {X Y : Scheme.{u}} (φ : Y ≅ X) {M N : X.Modules}
    (e : (Scheme.Modules.pullback φ.hom).obj M ≅ (Scheme.Modules.pullback φ.hom).obj N) : M ≅ N :=
  pullbackUnitIso φ M ≪≫ (Scheme.Modules.pullback φ.inv).mapIso e ≪≫ (pullbackUnitIso φ N).symm

end WSM

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

open scoped _root_.AlgebraicGeometry in
open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Modules in
open scoped _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
/-- An invertible module of the given Euler characteristic is a product of point inverses. -/
theorem exists_nonempty_iso_invModule_prod_ker_of_eulerChar_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) (r : ℕ)
    (h0 : 0 < Module.finrank K (𝒱.sectionsOf x M).H0)
    (hχ : (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
      (Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x
        (𝟙_ X.Modules)).H1 + r) :
    ∃ P : Fin r → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}, Nonempty (M ≅ (∏ m, (P
      m).1.ker).invModule) := by
  classical
  have : IsSeparated x := inferInstance
  obtain ⟨Pt, hPt, hPK, ⟨eY⟩⟩ :=
    exists_nonempty_pullback_fst_iso_invModule_prodKerGraph_of_eulerChar_eq
      K x hM 𝒱 r h0 hχ
  refine ⟨fun m => ⟨Pt m, hPt m⟩, ?_⟩
  let φ : Limits.pullback x (𝟙 (Spec (CommRingCat.of K))) ≅ X :=
    asIso (Limits.pullback.fst x (𝟙 (Spec (CommRingCat.of K))))
  have hI : (∏ m, (Pt m).ker).IsInvertible :=
    WSM.isInvertible_prod Finset.univ (fun m => (Pt m).ker)
      fun m _ => Scheme.Hom.isInvertible_ker_of_comp_eq_id (Pt m) (hPt m)
  have hcomap : (∏ m, (Pt m).ker).comap φ.hom = prodKerGraph x Pt hPt :=
    (WSM.prodKerGraph_eq_comap x Pt hPt).symm
  have hI' : ((∏ m, (Pt m).ker).comap φ.hom).IsInvertible := by
    rw [hcomap]; exact hPK
  obtain ⟨e93⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso φ.hom hI hI'
  have e₁ : (Scheme.Modules.pullback φ.hom).obj M ≅ (Scheme.Modules.pullback φ.hom).obj (∏ m, (Pt
    m).ker).invModule :=
    eY ≪≫ eqToIso (by rw [hcomap]) ≪≫ e93.symm
  exact ⟨WSM.isoOfPullbackIso φ e₁⟩

end AlgebraicGeometry.Scheme.Modules.IsInvertible

namespace WSM

/-- A two-affine cover is determined by its two open subsets. -/
theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

/-- A module isomorphism induces linear equivalences on two-chart cohomology. -/
theorem nonempty_linearEquiv_of_iso {R : Type u} [CommRing R] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X)
      (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

end WSM

end
end JacobianVarieties.Picard.Proofs.InjectiveTwistedSections

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicCurve hiding genus
open _root_.Opposite

namespace AlgebraicGeometry.RelPicard

universe u

open JacobianVarieties.Picard.Proofs.InjectiveTwistedSections in
open JacobianVarieties.Picard.Proofs.InjectiveTwistedSections.AlgebraicGeometry.Scheme.Modules in
open JacobianVarieties.Picard.Proofs.InjectiveTwistedSections.AlgebraicCurve.CurveModel in
/-- Choose distinct point sets so every permitted twist has vanishing first cohomology. -/
theorem exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {F : Type u} [Field F] [Algebra K F] (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x =
      M.toBase)
    (Kc : Divisor K F) (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1
      - g)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (r : ℕ) (hr : 2 * g ≤ r + 1)
    {ι : Type u} [Fintype ι]
    (B : ι → Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : r * b ^ (r - g) + (r - g) < Fintype.card ι)
    (hχ : ∀ (v : Fin (r - g) → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) (𝒱 :
      X.TwoAffineOpenCover),
      (Module.finrank K (𝒱.sectionsOf x (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H0 :
        ℤ) -
        Module.finrank K (𝒱.sectionsOf x (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H1
          = 1) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}, (∀ j, v j ∈ B (a j)) →
        ∀ 𝒱 : X.TwoAffineOpenCover,
          Subsingleton (𝒱.sectionsOf x (L ⊗ (((p.ker) ^ r).invModule ⊗ (∏ j, (v
            j).1.ker).module))).H1 := by
  classical
  have : IsSeparated x := inferInstance
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨U, V, hU, hV, hUV, hsup⟩ := AlgebraicCurve.exists_isAffineOpen_sup_eq_top x
    (fun F => AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset x F)
  let 𝒱₀ : X.TwoAffineOpenCover := ⟨U, V, hU, hV, hsup, hUV⟩
  have hpk : p.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp
  have hTw : Scheme.Modules.IsInvertible ((p.ker ^ r).invModule) := (hpk.pow
    r).isInvertible_invModule
  have hLT : Scheme.Modules.IsInvertible (L ⊗ (p.ker ^ r).invModule) := hL.tensor hTw
  obtain ⟨hS1, hh0⟩ :=
    subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero
      K x g hg p hp L hL h0 r hr 𝒱₀
  obtain ⟨hH1u, hH0u⟩ :=
    Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K x g hg 𝒱₀
  have hH1u' : Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H1 = g := hH1u
  have hH0u' : Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H0 = 1 := hH0u
  have h1LT : Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (p.ker ^ r).invModule)).H1 = 0 :=
    Module.finrank_zero_of_subsingleton
  have hχLT : (Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (p.ker ^ r).invModule)).H0 : ℤ)
        - Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (p.ker ^ r).invModule)).H1
      = (Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ)
        - Module.finrank K (𝒱₀.sectionsOf x (𝟙_ X.Modules)).H1 + r := by
    rw [hh0, h1LT, hH1u', hH0u']
    omega
  have hpos : 0 < Module.finrank K (𝒱₀.sectionsOf x (L ⊗ (p.ker ^ r).invModule)).H0 := by
    rw [hh0]; omega
  obtain ⟨Pt, ⟨eE⟩⟩ :=
    IsInvertible.exists_nonempty_iso_invModule_prod_ker_of_eulerChar_eq K x hLT 𝒱₀ r hpos hχLT
  obtain ⟨a, ha, hgood⟩ :=
    exists_injective_forall_forall_mem_ell_sum_single_pointEquivPlace_sub_eq_one
      x M e he hRR hr Pt B hdisj hb1 hb hcard
  refine ⟨a, ha, fun v hv 𝒱 => ?_⟩
  have hNI : (∏ j, (v j).1.ker).IsInvertible := by
    have key : ∀ s : Finset (Fin (r - g)), (∏ j ∈ s, (v j).1.ker).IsInvertible := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top] using
      Scheme.IdealSheafData.isInvertible_top
      | insert j s hj ih =>
        rw [Finset.prod_insert hj]
        exact (Scheme.Hom.isInvertible_ker_of_comp_eq_id (v j).1 (v j).2).mul ih
    exact key Finset.univ
  have hN : Scheme.Modules.IsInvertible (∏ j, (v j).1.ker).module := hNI.isInvertible_module
  have hTN : Scheme.Modules.IsInvertible ((p.ker ^ r).invModule ⊗ (∏ j, (v j).1.ker).module) :=
    hTw.tensor hN
  let eMN : L ⊗ ((p.ker ^ r).invModule ⊗ (∏ j, (v j).1.ker).module) ≅
      (∏ m, (Pt m).1.ker).invModule ⊗ (∏ j, (v j).1.ker).module :=
    (α_ L ((p.ker ^ r).invModule) ((∏ j, (v j).1.ker).module)).symm ≪≫
      whiskerRightIso eE ((∏ j, (v j).1.ker).module)
  obtain ⟨fin0, fin1, hrk⟩ :=
    AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
      x M e he Pt v 𝒱
  obtain ⟨⟨k0⟩, ⟨k1⟩⟩ := WSM.nonempty_linearEquiv_of_iso x 𝒱 eMN
  have hM0 : Module.finrank K (𝒱.sectionsOf x (L ⊗ ((p.ker ^ r).invModule ⊗ (∏ j, (v
    j).1.ker).module))).H0 = 1 :=
    k0.finrank_eq.trans (hrk.trans (hgood v hv))
  have : Module.Finite K (𝒱.sectionsOf x (L ⊗ ((p.ker ^ r).invModule ⊗ (∏ j, (v
    j).1.ker).module))).H1 :=
    Module.Finite.equiv k1.symm
  have hχc := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq x 𝒱 L
    ((p.ker ^ r).invModule ⊗ (∏ j, (v j).1.ker).module) hL hTN h0
  have hχv := hχ v 𝒱
  have hM1 : Module.finrank K (𝒱.sectionsOf x (L ⊗ ((p.ker ^ r).invModule ⊗ (∏ j, (v
    j).1.ker).module))).H1 = 0 := by
    omega
  exact Module.finrank_zero_iff.mp hM1

end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
  ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule
attribute [-instance]
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance]
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
attribute [-simp]
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
attribute [-simp]
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
  ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one
  AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
  AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
attribute [-simp]
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq
  AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply
  AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule
  AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one
  AlgebraicCurve.Place.mem_poleSubmodule
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.EndDegree
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafEulerChar
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafTensor
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
import Nyll.JacobianVarieties.Picard.RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_topologicalKrullDim_le
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_flat_of_isFinite
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_isIntegral_of_field
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_tensorPow_iso
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor

/-!
# Endomorphism degree and the Euler characteristic coefficient

This file compares the Euler characteristic polynomials of tensor powers of an invertible sheaf
and its pullback by a group-compatible endomorphism of an abelian scheme. In the relative
dimension, pullback multiplies the coefficient by the endomorphism degree.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.EndDegreeCoefficient
attribute [-instance]
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
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
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ
attribute [-instance]
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
attribute [-instance]
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsLocallyInjectiveFunUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.RelPicard.isOpenImmersion_toGlued
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
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
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  PresheafOfModules.ExteriorPower.instModulePresheafAb
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
  AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instNonempty
  AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
open _root_.AlgebraicGeometry.FGSubalgebra in
attribute [-instance]
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
  AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsFiltered
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
attribute [-instance]
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued
  AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀
  AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase
  AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase
  AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀
  AlgebraicCurve.CurveModel.isOpenImmersion_fInf
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase
  AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing
  AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing
  AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing
  AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
attribute [-instance]
  instTopologicallyFGOfFiniteType
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-simp]
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
attribute [-simp]
  AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  RegularLocalRingQuotientAscent.dualNumberFst_apply
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul
attribute [-simp]
  AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  CategoryTheory.Functor.OverTotal.ofFibre_fst
  CategoryTheory.Functor.overTotal_map_fst
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t'
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-simp]
  uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc
attribute [-simp]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ
attribute [-simp]
  AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
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
  AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv
attribute [-simp]
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
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
attribute [-simp]
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.fst_toProdSpec
  AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc
  AlgebraicGeometry.RelPicard.toProdSpec_fst
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
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp
  AlgebraicGeometry.RelEffCartierDiv.functor_map_fst
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq
  AlgebraicCurve.CurveModel.coe_gInf
  AlgebraicCurve.CurveModel.coe_tInvChart
  AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc
  AlgebraicCurve.CurveModel.ιInf_gluedToBase
  AlgebraicCurve.CurveModel.primeOfι₀_asIdeal
  AlgebraicCurve.CurveModel.coe_tChart
  AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc
  AlgebraicCurve.CurveModel.primeOfιInf_asIdeal
  AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_tma
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces
  AlgebraicGeometry.ProjSpace.twistObj.mk.injEq
  AlgebraicGeometry.ProjSpace.twistObj.zero_val
  AlgebraicGeometry.ProjSpace.twistObj.add_val
  AlgebraicGeometry.ProjSpace.twist_res_val
  AlgebraicGeometry.ProjSpace.twist_smul_val
  AlgebraicGeometry.ProjSpace.twistGradeToObj_val
  AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Opposite
open _root_.Polynomial

namespace P2mDegLead

open AlgebraicGeometry.OModulePresheaf

section Chi

variable {R : Type u} [CommRing R]

theorem eulerChar_eq_of_equiv {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (F' : OModulePresheaf π') (K : V.OrderedAffineCover) (K' :
      V'.OrderedAffineCover)
    (hcard : Fintype.card K.ι = Fintype.card K'.ι)
    (h0 : Nonempty (F.H0 K ≃ₗ[R] F'.H0 K')) (hs : ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F'.HSucc K'
      i)) :
    F.eulerChar K = F'.eulerChar K' := by
  have h : ∀ i, F.cechFinrank K i = F'.cechFinrank K' i := by
    intro i
    cases i with
    | zero => obtain ⟨e⟩ := h0; exact e.finrank_eq
    | succ j => obtain ⟨e⟩ := hs j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def, hcard]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π')
    (X : V.Modules)
    (K : V.OrderedAffineCover) : (ofModules π X).eulerChar K = (ofModules π' X).eulerChar K := by
  subst h; rfl

theorem isQuasicoherent_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π')
    (X : V.Modules)
    (hq : (ofModules π' X).IsQuasicoherent) : (ofModules π X).IsQuasicoherent := by
  subst h; exact hq

end Chi

section PushUnit

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem preimage_eq_bot (U : V.Opens) (hU : (U : Set V) = ∅) : ι ⁻¹ᵁ U = ⊥ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false]
  intro hz
  have : ι.base z ∈ (U : Set V) := hz
  rw [hU] at this
  exact this

theorem subsingleton_sections_of_eq_bot (W : Z.Opens) (h : W = ⊥) : Subsingleton Γ(Z, W) := by
  subst h
  infer_instance

theorem supportedIn_top : (pushforwardUnit π ι).SupportedIn ⊤ := fun U hU =>
  subsingleton_sections_of_eq_bot (ι ⁻¹ᵁ U.1)
    (preimage_eq_bot ι U.1 (by simpa only [Closeds.coe_top, Set.inter_univ] using hU))

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  change Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

theorem isCoherent [IsFinite ι] : (pushforwardUnit π ι).IsCoherent := by
  intro U
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := by
    ext a; exact appLE_rfl_apply ι U.1 a
  let : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hfin' : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact hfin
    exact this
  exact hfin'

theorem loc_core [IsAffineHom ι] (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens)
    (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y =
        Z.presheaf.map (homOfLE hle).op y := fun y => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1))
    (x : Γ(Z, ι ⁻¹ᵁ V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  change ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE
    (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U
        f)).op y) := by
  change Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le
    ι U f))]

theorem isQuasicoherent [IsAffineHom ι] : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U
    f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    have heval : Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
        Z.presheaf.map (homOfLE (pre_le ι U f)).op
          (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
          (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x) := by
      rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
      exact hy
    exact (res_eq π ι U f y).trans
      (heval.trans (smul_basicOpen π ι U f (f ^ n) x).symm)
  · intro y hy
    have hy' : Z.presheaf.map (homOfLE (pre_le ι U f)).op y = 0 :=
      (res_eq π ι U f y).symm.trans hy
    obtain ⟨n, hn⟩ := h2 y hy'
    refine ⟨n, ?_⟩
    have heval : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) *
        (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0 := by
      rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
      exact hn
    exact (smul_top π ι U (f ^ n) y).trans heval

end PushUnit

section Rank

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem finrank_comp_iso {X Y Y' : Scheme.{u}} (g : X ⟶ Y) [Flat g] [IsFinite g] (e : Y ≅ Y')
    (z : Y') :
    Scheme.Hom.finrank (g ≫ e.hom) z = Scheme.Hom.finrank g (e.inv.base z) := by
  have sq : IsPullback (𝟙 X) (g ≫ e.hom) g e.inv := IsPullback.of_horiz_isIso
    ⟨by simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z

theorem rankAtStalk_pushforwardUnit_obj [IsFinite ι] [Flat ι] (U : V.affineOpens) (r : ℕ)
    (hr : ∀ y : V, Scheme.Hom.finrank ι y = r) (𝔭 : PrimeSpectrum Γ(V, U.1)) :
    Module.rankAtStalk (R := Γ(V, U.1)) ((pushforwardUnit π ι).obj U.1) 𝔭 = r := by
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := Scheme.Hom.appLE_eq_app ι
  let alg : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by
      rw [heq]
      exact IsFinite.finite_app ι U.1 U.2
    exact this
  have : Module.Flat Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) (f := ι) inferInstance U ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩
        le_rfl
    exact this
  have key := Scheme.Hom.finrank_SpecMap_algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) 𝔭
  have hmap : CommRingCat.ofHom (algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1)) = ι.app U.1 := by
    rw [← heq]; rfl
  rw [hmap] at key
  have hU : IsAffineOpen U.1 := U.2
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have hnat : Spec.map (ι.app U.1) = hW.isoSpec.inv ≫ ((ι ∣_ U.1) ≫ hU.isoSpec.hom) := by
    rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  have hfr : Scheme.Hom.finrank (Spec.map (ι.app U.1)) 𝔭 = r := by
    let z : Spec Γ(V, U.1) := 𝔭
    change Scheme.Hom.finrank (Spec.map (ι.app U.1)) z = r
    rw [hnat, Scheme.Hom.finrank_comp_left_of_isIso, finrank_comp_iso,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict ι U.1).flip]
    exact hr _
  rw [hfr] at key
  exact key.symm

end Rank

section Setup

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

theorem krullDim_top_le (g : ℕ) [SmoothOfRelativeDimension g f] :
    topologicalKrullDim ((⊤ : Closeds A) : Set A) ≤ g :=
  (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g)

theorem exists_chart_prime [IsIntegral A] [Nonempty A] (𝒦 : A.OrderedAffineCover) :
    ∃ (U₀ : A.affineOpens) (𝔭 : PrimeSpectrum Γ(A, U₀.1)), (∃ i, U₀.1 = 𝒦.U i) ∧ 𝔭.asIdeal = ⊥ := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  have ha : a ∈ (⊤ : A.Opens) := trivial
  rw [← 𝒦.iSup_eq_top, Opens.mem_iSup] at ha
  obtain ⟨i, hi⟩ := ha
  have : Nonempty (𝒦.U i) := ⟨⟨a, hi⟩⟩
  exact ⟨⟨𝒦.U i, 𝒦.isAffineOpen i⟩, ⟨⊥, Ideal.isPrime_bot⟩, ⟨i, rfl⟩, rfl⟩

end Setup

section Chain

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem isInvertible_tensorPow {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (n : ℕ) :
    Scheme.Modules.IsInvertible (𝓛.tensorPow n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit A
  | succ n ih => exact ih.tensor h𝓛

variable [IsSeparated f] (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 :
  Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f) [IsAffineHom γ.1]

include h𝓛 in
theorem eulerChar_twist_eq (m : ℕ) :
    ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 := by
  have hN : Scheme.Modules.IsInvertible (𝓛.tensorPow m) := isInvertible_tensorPow h𝓛 m
  have e1 : ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)).eulerChar 𝒦 =
      (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar (𝒦.comap
        γ.1) := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit f γ.1 𝒦
      (𝓛.tensorPow m) hN.1
    exact (eulerChar_eq_of_equiv (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj
      (𝓛.tensorPow m)))
      ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)) (𝒦.comap γ.1) 𝒦 rfl h0 hs).symm
  have e2 := eulerChar_ofModules_congr γ.2 ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))
    (𝒦.comap γ.1)
  have hq : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial f _ (hN.pullback γ.1).1
  have e3 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar (𝒦.comap
    γ.1) =
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar 𝒦 := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f
      ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)) hq (𝒦.comap γ.1) 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))) (𝒦.comap γ.1) 𝒦 rfl h0 hs
  have e4 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso γ.1 𝓛 m
    obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso f e 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)) 𝒦 𝒦 rfl h0 hs
  rw [e1, e2, e3, e4]

end Chain

section Main

variable (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]
  (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f)
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
      L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
  (p q : Polynomial ℚ)
  (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
  (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ))

include hA hγ hp hq h𝓛 in
theorem main : p.coeff g = (L.endDegree γ : ℚ) * q.coeff g := by
  classical
  have : IsProper f := hA.proper
  have : Smooth f := hA.smooth
  have : ConnectedSpace A := connectedSpace hA
  have : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  by_cases hfin : IsFinite (L.endKerStr γ)
  swap
  · rw [L.endDegree_of_not_isFinite γ hfin, Nat.cast_zero, zero_mul]
    exact RelativeGroupLaw.coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
      K f L hA g 𝒦
      𝓛 h𝓛 γ hγ hfin p hp
  have : IsFinite (L.endKerStr γ) := hfin
  have : IsFinite γ.1 := RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L γ hγ
  have : Flat γ.1 := AbelianSchemePropertyBundle.flat_of_isFinite K hA γ
  obtain ⟨-, -, hrank⟩ := RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
    K f L γ
  set G : OModulePresheaf f := pushforwardUnit f γ.1 with hG
  have hGc : G.IsCoherent := isCoherent f γ.1
  have hGq : G.IsQuasicoherent := isQuasicoherent f γ.1
  have hGs : G.SupportedIn ⊤ := supportedIn_top f γ.1
  obtain ⟨p', -, hp'⟩ := exists_polynomial_forall_eulerChar_twist_tensorPow_eq f 𝒦 G hGc hGq ⊤ hGs g
    (krullDim_top_le (f := f) g) 𝓛 h𝓛.1
  have hpp : p' = p := by
    refine Polynomial.eq_of_infinite_eval_eq p' p
      ((Set.infinite_range_of_injective Nat.cast_injective).mono ?_)
    rintro _ ⟨m, rfl⟩
    change p'.eval (m : ℚ) = p.eval (m : ℚ)
    rw [← hp' m, ← hp m, hG, eulerChar_twist_eq f 𝒦 𝓛 h𝓛 γ m]
  obtain ⟨U₀, 𝔭, -, h𝔭⟩ := exists_chart_prime (A := A) 𝒦
  have hlead := coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq f 𝒦 𝓛 h𝓛.1 g
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g) q hq G hGc hGq p' hp' U₀ 𝔭 h𝔭
  have hrk : Module.rankAtStalk (R := Γ(A, U₀.1)) (G.obj U₀.1) 𝔭 = L.endDegree γ :=
    rankAtStalk_pushforwardUnit_obj f γ.1 U₀ (L.endDegree γ) (fun y => (hrank y).symm) 𝔭
  rw [← hpp, hlead, hrk]

end Main

end P2mDegLead
end JacobianVarieties.Picard.Proofs.EndDegreeCoefficient

namespace GoodReductionJacobian.RelativeGroupLaw

open _root_.JacobianVarieties.Picard.Proofs.EndDegreeCoefficient
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.TopologicalSpace
open _root_.Opposite
open _root_.Polynomial

/-- Pullback multiplies the Euler coefficient by the endomorphism degree. -/
theorem coeff_eq_endDegree_mul_coeff_of_forall_eulerChar_tensorPow_eq
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (p q : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
        (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
    (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m :
      ℚ)) :
    p.coeff g = (L.endDegree γ : ℚ) * q.coeff g :=
  P2mDegLead.main K f L hA g 𝒦 𝓛 h𝓛 γ hγ p q hp hq
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
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
  ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero
attribute [-instance]
  ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype
  ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq
  ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup
  ProjSpaceCech.Twist.cochain.instModule
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
attribute [-instance]
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsLocallyInjectiveFunUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-instance]
  instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf
attribute [-instance]
  AlgebraicGeometry.RelPicard.isOpenImmersion_toGlued
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
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
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase
  AlgebraicCurve.CurveModel.isFractionRing_overlap
  AlgebraicCurve.CurveModel.isLocallyNoetherian_glued
  AlgebraicCurve.CurveModel.jacobsonSpace_glued
  AlgebraicCurve.CurveModel.isOpenImmersion_ι₀
  AlgebraicCurve.CurveModel.isIntegral_glued
  AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase
  AlgebraicCurve.CurveModel.compactSpace_glued
  AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing
  AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField
  AlgebraicCurve.CurveModel.isProper_gluedToBase
  AlgebraicCurve.CurveModel.isOpenImmersion_ιU
  AlgebraicCurve.CurveModel.isOpenImmersion_f₀
  AlgebraicCurve.CurveModel.isOpenImmersion_fInf
  AlgebraicCurve.CurveModel.isOpenImmersion_ιInf
  AlgebraicCurve.CurveModel.algebra_overlap_functionField
  AlgebraicCurve.CurveModel.quasiCompact_gluedToBase
  AlgebraicCurve.CurveModel.algebraAdjoin
  AlgebraicCurve.CurveModel.isDedekindDomain_chartRing
  AlgebraicCurve.CurveModel.isIntegralClosure
  AlgebraicCurve.CurveModel.finite_chartRing
  AlgebraicCurve.CurveModel.centre_isPrime
  AlgebraicCurve.CurveModel.isFractionRing_chartRing
  AlgebraicCurve.CurveModel.finiteType_chartRing
  AlgebraicCurve.CurveModel.isNoetherianRing_chartRing
  AlgebraicCurve.CurveModel.isScalarTower_base_adjoin
  AlgebraicCurve.CurveModel.isScalarTower_adjoin
attribute [-instance]
  AlgebraicCurve.CurveModel.chartRing_finitePresentation
  instTopologicallyFGOfFiniteType
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
attribute [-simp]
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec
attribute [-simp]
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
  AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  RegularLocalRingQuotientAscent.dualNumberFst_apply
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul
  AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1
attribute [-simp]
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  CategoryTheory.Functor.OverTotal.ofFibre_fst
  CategoryTheory.Functor.overTotal_map_fst
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t'
open _root_.AlgebraicGeometry.Scheme.LocalRepresentabilityULift in
attribute [-simp]
  uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc
attribute [-simp]
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U
  AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P
  AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ
  AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
attribute [-simp]
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
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
attribute [-simp]
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one
  AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
  AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
attribute [-simp]
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
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.fst_toProdSpec
  AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc
  AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
attribute [-simp]
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
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp
  AlgebraicGeometry.RelEffCartierDiv.functor_map_fst
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  CoherentBaseChange.FibreH0Family.mk.sizeOf_spec
  CoherentBaseChange.FibreH0Family.mk.injEq
  AlgebraicCurve.CurveModel.coe_gInf
  AlgebraicCurve.CurveModel.coe_tInvChart
attribute [-simp]
  AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc
  AlgebraicCurve.CurveModel.ιInf_gluedToBase
  AlgebraicCurve.CurveModel.primeOfι₀_asIdeal
  AlgebraicCurve.CurveModel.coe_tChart
  AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc
  AlgebraicCurve.CurveModel.primeOfιInf_asIdeal
  AlgebraicCurve.CurveModel.ι₀_gluedToBase
  AlgebraicCurve.CurveModel.coe_tma
  AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces
  AlgebraicGeometry.ProjSpace.twistObj.mk.injEq
  AlgebraicGeometry.ProjSpace.twistObj.zero_val
  AlgebraicGeometry.ProjSpace.twistObj.add_val
  AlgebraicGeometry.ProjSpace.twist_res_val
  AlgebraicGeometry.ProjSpace.twist_smul_val
  AlgebraicGeometry.ProjSpace.twistGradeToObj_val
  AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec

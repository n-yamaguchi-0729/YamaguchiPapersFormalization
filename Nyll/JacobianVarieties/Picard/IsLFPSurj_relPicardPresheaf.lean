/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Schemes.AffineLimit
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.JacobianVarieties.Picard.LFP_exists_fg_nonempty_iso_pullbackAlong

import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
/-!
# Relative Picard varieties and fibre cohomology

Obtain finite-presentation surjectivity of the relative Picard presheaf from the line-bundle
pullback construction.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsLFPSurj_relPicardPresheaf
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
open _root_.AlgebraicGeometry.FGSubalgebra
  (instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram)
in
attribute [-instance]
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instNonempty
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
open _root_.AlgebraicGeometry.FGSubalgebra
  (instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram)
in
attribute [-instance]
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
attribute [-instance] AlgebraicGeometry.FGSubalgebra.instIsFiltered
attribute [-instance] AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
attribute [-instance] AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
attribute [-instance] SheafOfModules.instFaithfulRingSheafPModToPMod
attribute [-instance] SheafOfModules.symmetricCategory
attribute [-instance] AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
attribute [-instance] AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
attribute [-instance] SheafOfModules.instFullRingSheafPModToPMod
attribute [-instance] SheafOfModules.monoidalCategory
attribute [-instance] AlgebraicGeometry.Scheme.Modules.symmetricCategory
attribute [-instance] SheafOfModules.monoidalClosed
attribute [-instance] SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
attribute [-instance] SheafOfModules.sheafifyFunctor_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.monoidalClosed
attribute [-instance] AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
attribute [-instance] AlgebraicGeometry.Scheme.Modules.monoidalCategory
attribute [-instance] PresheafOfModules.instMonoidalClosed
open _root_.PresheafOfModules.InternalHom
  (instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies)
in
attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
open _root_.PresheafOfModules.InternalHom
  (instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf)
in
attribute [-instance]
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
open _root_.PresheafOfModules.InternalHom
  (instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies)
in
attribute [-instance]
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ
attribute [-instance] PresheafOfModules.pushforward_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_η
attribute [-instance] PresheafOfModules.free_monoidal
attribute [-instance] PresheafOfModules.restrictScalars_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ_gS
attribute [-instance] PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb)
in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance] PresheafOfModules.pullback_monoidal'
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
attribute [-instance] AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
attribute [-instance] AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec
  GoodReductionJacobian.AvatarSchemeBridge.mk.injEq
  GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.injEq
  GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply
  NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
attribute [-simp] PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem _root_.AlgebraicGeometry.RelPicard.isLFPSurj_relPicardPresheaf
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec
      (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPSurj (relPicardPresheaf c ε) := by
  intro A _ _ x
  induction x using Quotient.inductionOn with
  | h M =>
  obtain ⟨A₀, hA₀, M₀, hiso⟩ :=
    AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong R 𝒱 c ε A M
  exact ⟨A₀, hA₀, Quotient.mk _ M₀, Quotient.sound hiso⟩
end JacobianVarieties.Picard.Proofs.IsLFPSurj_relPicardPresheaf
end ProofImplementation

attribute [-simp] AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec
  GoodReductionJacobian.AvatarSchemeBridge.mk.injEq
  GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.injEq
  GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply
  NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
attribute [-simp] PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.JacobianVarieties.Picard.IsSheafFor_relSubPicPresheaf_algEquivZeroCut_finiteEtale_of_finiteMapData
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_representableBy_of_representableBy_restrict_finiteEtale
import Nyll.AlgebraicCurves.Geometry.Curves.smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
Descend a relative Picard representation along a finite etale faithfully flat extension.
-/
section ProofImplementation

namespace AlgebraicGeometry.RelPicard
attribute [-instance]
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  PresheafOfModules.instMonoidalClosed
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
attribute [-instance]
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
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
attribute [-instance]
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
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
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  Algebra.DescentCofaces.i₁_apply
  Algebra.DescentCofaces.i₂_apply
  Algebra.DescentCofaces.c₁₂_tmul
  Algebra.DescentCofaces.c₂₃_tmul
  Algebra.DescentCofaces.c₁₃_tmul
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
attribute [-simp]
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
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
attribute [-simp]
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero
attribute [-simp]
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicGeometry.DescentAction.toTriple_fst_assoc
  AlgebraicGeometry.DescentAction.invol_snd_assoc
  AlgebraicGeometry.DescentAction.unitMap_fst
  AlgebraicGeometry.DescentAction.flipMap_snd_assoc
  AlgebraicGeometry.DescentAction.actMap_snd_assoc
  AlgebraicGeometry.DescentAction.unitMap_fst_assoc
  AlgebraicGeometry.DescentAction.unitMap_snd
  AlgebraicGeometry.DescentAction.eRel_snd
  AlgebraicGeometry.DescentAction.toTriple_fst
  AlgebraicGeometry.DescentAction.invol_invol
  AlgebraicGeometry.DescentAction.proj₁₃_snd
  AlgebraicGeometry.DescentAction.eRel_snd_assoc
  AlgebraicGeometry.DescentAction.invol_invol_assoc
  AlgebraicGeometry.DescentAction.invol_act
  AlgebraicGeometry.DescentAction.actMap_fst_assoc
  AlgebraicGeometry.DescentAction.flipMap_fst_assoc
  AlgebraicGeometry.DescentAction.eRel_fst_assoc
  AlgebraicGeometry.DescentAction.eRel_fst
  AlgebraicGeometry.DescentAction.invol_act_assoc
  AlgebraicGeometry.DescentAction.invol_fst_assoc
  AlgebraicGeometry.DescentAction.proj₁₃_snd_assoc
  AlgebraicGeometry.DescentAction.mk.injEq
  AlgebraicGeometry.DescentAction.flipMap_fst
  AlgebraicGeometry.DescentAction.proj₁₃_fst
  AlgebraicGeometry.DescentAction.invol_fst
  AlgebraicGeometry.DescentAction.unitMap_snd_assoc
  AlgebraicGeometry.DescentAction.actMap_fst
  AlgebraicGeometry.DescentAction.toTriple_snd_assoc
  AlgebraicGeometry.DescentAction.invol_snd
  AlgebraicGeometry.DescentAction.actMap_snd
  AlgebraicGeometry.DescentAction.flipMap_snd
  AlgebraicGeometry.DescentAction.proj₁₃_fst_assoc
  AlgebraicGeometry.DescentAction.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.DescentAction.toTriple_snd

universe u

open  CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite
/-- Descend a relative Picard representation and its geometric properties along a finite etale
faithfully flat extension. -/
theorem exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶
      Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Algebra.Etale R R']
    [Module.FaithfullyFlat R R']
    (D' : RelativePic0Designation R' (baseChange R c R'))
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) D')
    (hsm : Smooth D'.toBase) (hpr : IsProper D'.toBase) (hgc : GeometricallyConnected D'.toBase)
    (haff : ∀ S : Finset D'.P, ∃ U : D'.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        ∃ e : pullback D.toBase (specMap R R') ≅ D'.P,
          e.hom ≫ D'.toBase = pullback.snd D.toBase (specMap R R') := by
  have hrep' := BaseChange.representableByRestrict c ε R' h'
  obtain ⟨X, f, rep, e, he⟩ :=
    AlgebraicGeometry.exists_representableBy_of_representableBy_restrict_finiteEtale
    R R' (relSubPicPresheaf c ε (algEquivZeroCut c ε))
    (isSheafFor_relSubPicPresheaf_algEquivZeroCut_finiteEtale_of_finiteMapData
      R c ε h𝔉 R')
    D'.toBase hrep' haff
  obtain ⟨hs, hp, hg⟩ :=
    AlgebraicGeometry.smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange R R' f
      D'.toBase
      hsm hpr hgc e he
  let u₀ : (relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of
    R))))) :=
    ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), (algEquivZeroCut c ε).unit_mem (𝟙 _)⟩
  let z : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk f := rep.homEquiv.symm u₀
  let D : RelativePic0Designation R c :=
    { P := X, toBase := f, zeroSection := z.left, zeroSection_toBase := Over.w z }
  have hz : (Over.homMk D.zeroSection D.zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase) = z := Over.OverMorphism.ext rfl
  have h0 : (rep.homEquiv (Over.homMk D.zeroSection D.zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)) := by
    rw [hz]
    change (rep.homEquiv (rep.homEquiv.symm u₀)).1 = _
    rw [Equiv.apply_symm_apply]
  exact ⟨D, RepresentsRelSubPic.nonempty_of_representableBy rep h0, hs, hp, hg, e, he⟩
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  Algebra.DescentCofaces.i₁_apply
  Algebra.DescentCofaces.i₂_apply
  Algebra.DescentCofaces.c₁₂_tmul
  Algebra.DescentCofaces.c₂₃_tmul
attribute [-simp]
  Algebra.DescentCofaces.c₁₃_tmul
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
attribute [-simp]
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
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
attribute [-simp]
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
  AlgebraicGeometry.DescentAction.toTriple_fst_assoc
  AlgebraicGeometry.DescentAction.invol_snd_assoc
  AlgebraicGeometry.DescentAction.unitMap_fst
  AlgebraicGeometry.DescentAction.flipMap_snd_assoc
  AlgebraicGeometry.DescentAction.actMap_snd_assoc
  AlgebraicGeometry.DescentAction.unitMap_fst_assoc
  AlgebraicGeometry.DescentAction.unitMap_snd
  AlgebraicGeometry.DescentAction.eRel_snd
  AlgebraicGeometry.DescentAction.toTriple_fst
  AlgebraicGeometry.DescentAction.invol_invol
  AlgebraicGeometry.DescentAction.proj₁₃_snd
  AlgebraicGeometry.DescentAction.eRel_snd_assoc
  AlgebraicGeometry.DescentAction.invol_invol_assoc
  AlgebraicGeometry.DescentAction.invol_act
  AlgebraicGeometry.DescentAction.actMap_fst_assoc
  AlgebraicGeometry.DescentAction.flipMap_fst_assoc
  AlgebraicGeometry.DescentAction.eRel_fst_assoc
  AlgebraicGeometry.DescentAction.eRel_fst
  AlgebraicGeometry.DescentAction.invol_act_assoc
  AlgebraicGeometry.DescentAction.invol_fst_assoc
  AlgebraicGeometry.DescentAction.proj₁₃_snd_assoc
  AlgebraicGeometry.DescentAction.mk.injEq
  AlgebraicGeometry.DescentAction.flipMap_fst
  AlgebraicGeometry.DescentAction.proj₁₃_fst
  AlgebraicGeometry.DescentAction.invol_fst
  AlgebraicGeometry.DescentAction.unitMap_snd_assoc
  AlgebraicGeometry.DescentAction.actMap_fst
  AlgebraicGeometry.DescentAction.toTriple_snd_assoc
attribute [-simp]
  AlgebraicGeometry.DescentAction.invol_snd
  AlgebraicGeometry.DescentAction.actMap_snd
  AlgebraicGeometry.DescentAction.flipMap_snd
  AlgebraicGeometry.DescentAction.proj₁₃_fst_assoc
  AlgebraicGeometry.DescentAction.mk.sizeOf_spec
  AlgebraicGeometry.DescentAction.toTriple_snd

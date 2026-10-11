/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.LinearAlgebra.Dimension.Finrank
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import AlgebraicCurves.Cohomology.Sheaves.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

/-!
# Rel Eff Cartier Div exists I eq zero Scheme Ideal and supported In of support subset of is
Open Immersion
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.OpenCartierIdealExtension
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
open AlgebraicCurve.Divisor in
attribute [-instance]
  instDistribMulActionAlgEquiv
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instSMulAlgEquiv
  instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
open AlgebraicCurve.Pic0 in
attribute [-instance]
  instDistribMulActionAlgEquiv
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instAlgebraSubtypeMemValuationSubringToValuationSubring
  instMulActionAlgEquiv
open AlgebraicCurve.Pic0 in
attribute [-instance]
  instSMulAlgEquiv
open AlgebraicCurve.CurveModel in
attribute [-instance]
  isProper
  isIntegral
  smooth
open AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
open AlgebraicGeometry.RelEffCartierDiv in
attribute [-instance]
  isIso_subschemeIota_snd_of_degree_one
open AlgebraicGeometry in
attribute [-instance]
  isIso_ker_graphOver_subschemeIota_snd
  isClosedImmersion_graphOver
open _root_.SheafOfModules in
attribute [-instance]
  isIso_ihomModelToIhom
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-instance] ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
attribute [-simp] AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
attribute [-simp] ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


universe u

noncomputable section

namespace M16Child

theorem map_eq_zero_iff_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (s : M
  ⟶ N) :
    (Scheme.Modules.pullback f).map s = 0 ↔ s = 0 := by
  let e : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (inv f) ≅ 𝟭 _ :=
    Scheme.Modules.pullbackComp (inv f) f ≪≫ Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫
      Scheme.Modules.pullbackId Y
  have : (Scheme.Modules.pullback f).Faithful := Functor.Faithful.of_comp_iso e
  constructor
  · intro h
    apply (Scheme.Modules.pullback f).map_injective
    exact h.trans (Functor.map_zero _ _ _).symm
  · intro h
    subst h
    exact Functor.map_zero _ _ _

theorem pullbackSection_ne_zero_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] {M : Y.Modules}
    (s : 𝟙_ Y.Modules ⟶ M) (hs : s ≠ 0) : Scheme.Modules.pullbackSection f s ≠ 0 := by
  intro h
  apply hs
  have h0 : (Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s =
      (0 : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback f).obj M) := h
  have h1 : (Scheme.Modules.pullback f).map s =
      (Scheme.Modules.pullbackUnitIso f).hom ≫
        ((Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) :=
    (Iso.hom_inv_id_assoc _ _).symm
  have h2 := congrArg (fun t => (Scheme.Modules.pullbackUnitIso f).hom ≫ t) h0
  exact (map_eq_zero_iff_of_isIso f s).1 ((h1.trans h2).trans Limits.comp_zero)

theorem twoAffineOpenCover_ext {X : Scheme.{u}} (𝒱₁ 𝒱₂ : X.TwoAffineOpenCover)
    (h0 : 𝒱₁.U0 = 𝒱₂.U0) (h1 : 𝒱₁.U1 = 𝒱₂.U1) : 𝒱₁ = 𝒱₂ := by
  rcases 𝒱₁ with ⟨U0, U1, a1, a2, a3, a4⟩
  rcases 𝒱₂ with ⟨V0, V1, b1, b2, b3, b4⟩
  simp only at h0 h1
  subst h0 h1
  rfl

end M16Child
end
end AlgebraicCurves.RelativeDivisors.Proofs.OpenCartierIdealExtension

namespace AlgebraicGeometry.RelEffCartierDiv
noncomputable section

open _root_.AlgebraicCurves.RelativeDivisors.Proofs.OpenCartierIdealExtension
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
universe u


open M16Child in
theorem exists_I_eq_zeroSchemeIdeal_and_supportedIn_of_support_subset_of_isOpenImmersion
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] [SmoothOfRelativeDimension 1 y] [GeometricallyIrreducible y]
    (i : Y ⟶ pullback c x) (hi : i ≫ pullback.snd c x = y)
    (W₁ : (pullback c x).Opens) [IsOpenImmersion ((i ⁻¹ᵁ W₁).ι ≫ i)]
    (hW₁ : (W₁ : Set ↥(pullback c x)) ⊆ Set.range i.base)
    (hWU : W₁ ≤ (pullback.fst c x) ⁻¹ᵁ U)
    (M : (pullback c x).Modules) (hM : Scheme.Modules.IsInvertible M)
    (σ : 𝟙_ (pullback c x).Modules ⟶ M)
    (hsupp : ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c x)) ⊆ (W₁ : Set
      ↥(pullback c x)))
    (hσ : Scheme.Modules.pullbackSection i σ ≠ 0)
    (g : ℕ) (𝒱 : Y.TwoAffineOpenCover)
    (hχ : (Module.finrank k (𝒱.sectionsOf y ((Scheme.Modules.pullback i).obj M)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf y ((Scheme.Modules.pullback i).obj M)).H1
      = (Module.finrank k (𝒱.sectionsOf y (𝟙_ Y.Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf y (𝟙_ Y.Modules)).H1 + g) :
    ∃ D : RelEffCartierDiv c g x, D.I = Scheme.Modules.zeroSchemeIdeal σ ∧ D.SupportedIn U := by
  have hMY : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback i).obj M) := hM.pullback i
  have hKY_comap : (Scheme.Modules.zeroSchemeIdeal σ).comap i =
      Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ) :=
    Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i hM σ
  set φ : pullback y (𝟙 (Spec (CommRingCat.of k))) ⟶ Y := pullback.fst y (𝟙 _) with hφdef
  have : IsIso φ := by rw [hφdef]; infer_instance
  have hφy : φ ≫ y = pullback.snd y (𝟙 _) := by
    rw [hφdef, pullback.condition, Category.comp_id]
  have hMP : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback i).obj M)) := hMY.pullback φ
  have hsP : Scheme.Modules.pullbackSection φ (Scheme.Modules.pullbackSection i σ) ≠ 0 :=
    pullbackSection_ne_zero_of_isIso φ _ hσ
  obtain ⟨𝒱P, hχP⟩ : ∃ 𝒱P : (pullback y (𝟙 (Spec (CommRingCat.of k)))).TwoAffineOpenCover,
      (Module.finrank k (𝒱P.sectionsOf (pullback.snd y (𝟙 _))
          ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback i).obj M))).H0 : ℤ)
        - Module.finrank k (𝒱P.sectionsOf (pullback.snd y (𝟙 _))
          ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback i).obj M))).H1
      = (Module.finrank k (𝒱P.sectionsOf (pullback.snd y (𝟙 _))
          (𝟙_ (pullback y (𝟙 (Spec (CommRingCat.of k)))).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱P.sectionsOf (pullback.snd y (𝟙 _))
          (𝟙_ (pullback y (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1 + g := by
    have hφy' : (asIso φ).hom ≫ y = pullback.snd y (𝟙 _) := by rw [asIso_hom, hφy]
    obtain ⟨𝒱₁, h10, h11, ⟨eH0⟩, ⟨eH1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (pullback.snd y (𝟙 _)) y
        (asIso φ) hφy' 𝒱
        ((Scheme.Modules.pullback i).obj M) ((Scheme.Modules.pullback φ).obj
          ((Scheme.Modules.pullback i).obj M))
        (Iso.refl _)
    obtain ⟨𝒱₂, h20, h21, ⟨fH0⟩, ⟨fH1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (pullback.snd y (𝟙 _)) y
        (asIso φ) hφy' 𝒱
        (𝟙_ Y.Modules) (𝟙_ (pullback y (𝟙 (Spec (CommRingCat.of k)))).Modules)
        (Scheme.Modules.pullbackUnitIso φ).symm
    have h12 : 𝒱₂ = 𝒱₁ := twoAffineOpenCover_ext _ _ (h20.trans h10.symm) (h21.trans h11.symm)
    subst h12
    refine ⟨𝒱₂, ?_⟩
    have e1 := eH0.finrank_eq
    have e2 := eH1.finrank_eq
    have e3 := fH0.finrank_eq
    have e4 := fH1.finrank_eq
    convert hχ using 4
  obtain ⟨DP, hDP, -⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
    (f := y) (𝟙 (Spec (CommRingCat.of k))) hMP _ hsP 𝒱P g hχP
  have hDPI : DP.I = (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap φ
    := by
    rw [hDP, Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal φ hMY]
  have hfinP : IsFinite (((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i
    σ)).comap φ).subschemeι ≫
      pullback.snd y (𝟙 _)) := by rw [← hDPI]; exact DP.isFinite
  have hflatP : Flat (((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap
    φ).subschemeι ≫
      pullback.snd y (𝟙 _)) := by rw [← hDPI]; exact DP.flat
  have hlfpP : LocallyOfFinitePresentation
      (((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap φ).subschemeι ≫
        pullback.snd y (𝟙 _)) := by rw [← hDPI]; exact DP.locallyOfFinitePresentation
  have hdegP : ∀ t, ((((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap
    φ).subschemeι ≫
      pullback.snd y (𝟙 _))).finrank t = g := by rw [← hDPI]; exact DP.finrank_eq
  have hsupp₁ : ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).support :
    Set Y) ⊆
      Set.range (i ⁻¹ᵁ W₁).ι := by
    intro p hp
    rw [← hKY_comap, Scheme.IdealSheafData.support_comap] at hp
    rw [Scheme.Opens.range_ι]
    exact hsupp hp
  obtain ⟨e₁, he₁⟩ := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)) (i ⁻¹ᵁ W₁).ι hsupp₁
  have hsupp₂ : ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c x)) ⊆
      Set.range ((i ⁻¹ᵁ W₁).ι ≫ i) := by
    intro z hz
    have hzW : z ∈ W₁ := hsupp hz
    obtain ⟨y0, hy0⟩ := hW₁ hzW
    have hy0W : y0 ∈ i ⁻¹ᵁ W₁ := by
      change i.base y0 ∈ W₁
      rw [hy0]; exact hzW
    refine ⟨(⟨y0, hy0W⟩ : (i ⁻¹ᵁ W₁).toScheme), ?_⟩
    change i.base y0 = z
    exact hy0
  have hcomp : (Scheme.Modules.zeroSchemeIdeal σ).comap ((i ⁻¹ᵁ W₁).ι ≫ i) =
      (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap (i ⁻¹ᵁ W₁).ι := by
    rw [Scheme.IdealSheafData.comap_comp, hKY_comap]
  have h2 := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    (Scheme.Modules.zeroSchemeIdeal σ) ((i ⁻¹ᵁ W₁).ι ≫ i) hsupp₂
  rw [hcomp] at h2
  obtain ⟨e₂, he₂⟩ := h2
  obtain ⟨e₃, he₃⟩ := Scheme.IdealSheafData.exists_iso_subscheme_comap_of_support_subset_range
    (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)) φ
    (by intro z _; exact ⟨(inv φ).base z, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩)
  have hfac : (Scheme.Modules.zeroSchemeIdeal σ).subschemeι ≫ pullback.snd c x =
      (e₂.inv ≫ e₁.hom ≫ e₃.inv) ≫
        ((((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap
          φ).subschemeι ≫
          pullback.snd y (𝟙 _))) := by
    have hA : (Scheme.Modules.zeroSchemeIdeal σ).subschemeι =
        e₂.inv ≫ ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap (i
          ⁻¹ᵁ W₁).ι).subschemeι ≫
          (i ⁻¹ᵁ W₁).ι ≫ i := by
      rw [← he₂, Iso.inv_hom_id_assoc]
    have hB : ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap (i ⁻¹ᵁ
      W₁).ι).subschemeι ≫
        (i ⁻¹ᵁ W₁).ι = e₁.hom ≫ (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i
          σ)).subschemeι := he₁.symm
    have hC : (Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).subschemeι =
        e₃.inv ≫ ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i σ)).comap
          φ).subschemeι ≫ φ := by
      rw [← he₃, Iso.inv_hom_id_assoc]
    rw [hA]
    simp only [Category.assoc]
    rw [hi, ← Category.assoc ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection i
      σ)).comap
      (i ⁻¹ᵁ W₁).ι).subschemeι, hB, Category.assoc, hC]
    simp only [Category.assoc]
    rw [hφy]
  refine ⟨⟨Scheme.Modules.zeroSchemeIdeal σ, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · rw [hfac]; have := hfinP; infer_instance
  · rw [hfac]; have := hflatP; infer_instance
  · rw [hfac]; have := hlfpP; infer_instance
  · intro t; rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso]; exact hdegP t
  · intro z hz; exact hWU (hsupp hz)
end
end AlgebraicGeometry.RelEffCartierDiv
end ProofImplementation

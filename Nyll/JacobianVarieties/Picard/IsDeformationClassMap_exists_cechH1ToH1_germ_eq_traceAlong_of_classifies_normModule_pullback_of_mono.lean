/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.Topology.Irreducible
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverKaehler
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSerrePairingInt
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.Cech.Maps
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumberBaseTransport
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_baseChange
import Nyll.JacobianVarieties.Picard.RigKerDualNumber_existsUnique_kerPoint_baseChange_comp_fst_eq
import Nyll.JacobianVarieties.Picard.RigKerDualNumber_kerPointsToRigKer_baseTransport
import Nyll.JacobianVarieties.Picard.exists_isDeformationClassMap
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_apply_baseTransport_eq_H1baseChangeMap
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange
import Nyll.AlgebraicCurves.Cohomology.CechH1ToH1_corrH1_of_pullback_specMap_self

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Trace on deformation classes after a monomorphic base change
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard.IsDeformationClassMap
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicCurve
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

/-- The field trace description descends along a monomorphic base change. -/
theorem exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_mono
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    [Mono (specMap R K)]
    [IsIntegral (Limits.pullback c (specMap R K))]
    [IsSeparated (pullback.snd c (specMap R K))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (specMap R K))]
    (hC : ∀ Z : Set ↥(Limits.pullback c (specMap R K)), IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (.of K)) [IsIntegral Y] [IsProper y] [SmoothOfRelativeDimension
      1 y]
    (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y ≫ specMap R K) (Hβ : πβ ≫ c = y ≫ specMap R K)
    [IsFinite (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [Flat (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [LocallyOfFinitePresentation (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K))]
    [IsAffineHom (pullback.lift πβ y Hβ : Y ⟶ Limits.pullback c (specMap R K))]
    (d : ℕ) (hd : ∀ z, (pullback.lift πα y Hα : Y ⟶ Limits.pullback c (specMap R K)).finrank z = d)
    (φ₁ : SchemeHomOver D.toBase D.toBase)
    (hmoduli :
      ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (.of K))
          (M : RigidifiedLineBundle c ε (t' ≫ specMap R K))
          (hM : (algEquivZeroCut c ε).P (t' ≫ specMap R K) M),
        Nonempty ((h.poincare.pullbackAlong
            (NeronModelInfra.schemeHomOverComp (h.classify (t' ≫ specMap R K) M hM) φ₁)).L ≅
          Scheme.Modules.rigidify (rigSection c (t' ≫ specMap R K) ε) (pullback.snd c (t' ≫ specMap
            R K))
            (Scheme.Modules.normModule (curveChange (c' := y ≫ specMap R K) πα Hα (t' ≫ specMap R
              K)) d
              ((Scheme.Modules.pullback (curveChange (c' := y ≫ specMap R K) πβ Hβ (t' ≫ specMap R
                K))).obj M.L))))
    (𝒲 : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε K → H1StructureSheaf c K 𝒲} (hδ : IsDeformationClassMap c ε K 𝒲 δ)
    (x xr : {x : SchemeHomOver (specMap R (DualNumber K)) D.toBase //
        dualNumberReduction R K ≫ x.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (specMap R
            K)).1})
    (hxr : xr.1.1 = x.1.1 ≫ φ₁.1)
    (s : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01)
    (hs : δ (h.kerPointsToRigKer K x) = Submodule.Quotient.mk s) :
    let X' : Scheme.{u} := Limits.pullback c (specMap R K)
    let c' : X' ⟶ Spec (.of K) := pullback.snd c (specMap R K)
    let _ : Algebra K X'.functionField := (AlgebraicCurve.baseToFunctionField c').toAlgebra
    let _ : Algebra K Y.functionField := (AlgebraicCurve.baseToFunctionField y).toAlgebra
    let W : X'.TwoAffineOpenCover := 𝒲.pullback c K
    ∀ [Nonempty (W.U0 ⊓ W.U1 : X'.Opens)]
      (φα φβ : X'.functionField →ₐ[K] Y.functionField),
      (Y.fromSpecStalk (genericPoint Y) ≫ pullback.lift πα y Hα =
        Spec.map (CommRingCat.ofHom φα.toRingHom) ≫ X'.fromSpecStalk (genericPoint X')) →
      (Y.fromSpecStalk (genericPoint Y) ≫ pullback.lift πβ y Hβ =
        Spec.map (CommRingCat.ofHom φβ.toRingHom) ≫ X'.fromSpecStalk (genericPoint X')) →
      ∀ (hφα : φα.toRingHom.IsIntegral) (hφβ : φβ.toRingHom.IsIntegral) (htrα : TraceIntegralAlong
        φα hφα)
      (hW : AlgebraicCurve.placesOf c' W.U0 ∪ AlgebraicCurve.placesOf c' W.U1 = Set.univ)
      (hsr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s ∈
        AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K X'.functionField)),
      ∃ (sr : ((𝒲.pullback c K).cover (pullback.snd c (specMap R K))).A01)
        (hsrr : (X'.germToFunctionField (W.U0 ⊓ W.U1)).hom sr ∈
          AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf c' W.U0 ∩ AlgebraicCurve.placesOf c'
            W.U1)
            (0 : AlgebraicCurve.Divisor K X'.functionField))
        (x' : AlgebraicCurve.cechH1 ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹'
          AlgebraicCurve.placesOf c' W.U0)
          ((AlgebraicCurve.Place.restrictAlong φα hφα) ⁻¹' AlgebraicCurve.placesOf c' W.U1)
          (0 : AlgebraicCurve.Divisor K Y.functionField)),
        δ (h.kerPointsToRigKer K xr) = Submodule.Quotient.mk sr ∧
        AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φα hφα hW) 0
          x' =
          AlgebraicCurve.cechH1ToH1 (AlgebraicCurve.preimage_restrictAlong_union_eq_univ φβ hφβ hW)
            0
            (AlgebraicCurve.cechH1.pullbackAlong φβ hφβ _ _
              (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom s, hsr⟩)) ∧
        AlgebraicCurve.cechH1ToH1 hW 0
            (Submodule.Quotient.mk ⟨(X'.germToFunctionField (W.U0 ⊓ W.U1)).hom sr, hsrr⟩) =
          AlgebraicCurve.cechH1ToH1 hW 0 (AlgebraicCurve.cechH1.traceAlong φα hφα htrα _ _ x') := by
  intro X' c' algXFunctionField algYFunctionField W instNE φα φβ hφπα hφπβ hφα hφβ htrα hW hsr
  have hbaseRepresentation := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange R c
    ε D h K
  let h' : RepresentsRelSubPic (SmoothProperCurve.baseChange R c K)
    (SmoothProperCurve.sectionBaseChange K ε)
      (algEquivZeroCut (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K
        ε))
      (D.baseChange K) := hbaseRepresentation.choose
  have hP := hbaseRepresentation.choose_spec
  have hkerX :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq c ε D
      h K h' hP K x
  let x₁ : { x' : SchemeHomOver (specMap K (DualNumber K)) (D.baseChange K).toBase //
      dualNumberReduction K K ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (SmoothProperCurve.baseChange R c K)
            (SmoothProperCurve.sectionBaseChange K ε)) h').one (specMap K K)).1 } := hkerX.choose
  have hx₁ : x₁.1.1 ≫ pullback.fst D.toBase (specMap R K) = x.1.1 := hkerX.choose_spec.1
  have hkerXr :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.existsUnique_kerPoint_baseChange_comp_fst_eq c ε D
      h K h' hP K xr
  let xr₁ : { x' : SchemeHomOver (specMap K (DualNumber K)) (D.baseChange K).toBase //
      dualNumberReduction K K ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (SmoothProperCurve.baseChange R c K)
            (SmoothProperCurve.sectionBaseChange K ε)) h').one (specMap K K)).1 } :=
    hkerXr.choose
  have hxr₁ : xr₁.1.1 ≫ pullback.fst D.toBase (specMap R K) = xr.1.1 := hkerXr.choose_spec.1
  let φ₁K : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase :=
    ⟨pullback.lift (pullback.fst D.toBase (specMap R K) ≫ φ₁.1) (pullback.snd D.toBase (specMap R
      K))
        (by rw [Category.assoc, φ₁.2]; exact pullback.condition),
      pullback.lift_snd _ _ _⟩
  have hφ₁K : φ₁K.1 ≫ pullback.fst D.toBase (specMap R K) = pullback.fst D.toBase (specMap R K) ≫
    φ₁.1 :=
    pullback.lift_fst _ _ _
  have hxr₁' : xr₁.1.1 = x₁.1.1 ≫ φ₁K.1 := by
    apply pullback.hom_ext
    · rw [hxr₁, Category.assoc, hφ₁K, ← Category.assoc, hx₁, hxr]
    · rw [Category.assoc]
      exact xr₁.1.2.trans (x₁.1.2.symm.trans (by rw [φ₁K.2]))
  have Hα₁ : pullback.lift πα y Hα ≫ SmoothProperCurve.baseChange R c K = y := pullback.lift_snd _
    _ _
  have Hβ₁ : pullback.lift πβ y Hβ ≫ SmoothProperCurve.baseChange R c K = y := pullback.lift_snd _
    _ _
  have hmoduli₁ := fun (T : Scheme.{u}) (t : T ⟶ Spec (.of K)) M hM =>
    RepresentsRelSubPic.nonempty_poincare_pullbackAlong_iso_rigidify_normModule_baseChange c ε K D
      h h' hP y πα πβ Hα Hβ d hd φ₁ hmoduli φ₁K hφ₁K Hα₁ Hβ₁ T t M hM
  have hdeformationMap := AlgebraicGeometry.RelPicard.exists_isDeformationClassMap
    (SmoothProperCurve.baseChange R c K) (SmoothProperCurve.sectionBaseChange K ε) K (𝒲.pullback c
      K)
  let δ₁ : RigKerDualNumber (SmoothProperCurve.baseChange R c K)
    (SmoothProperCurve.sectionBaseChange K ε) K →
      H1StructureSheaf (SmoothProperCurve.baseChange R c K) K (𝒲.pullback c K) :=
        hdeformationMap.choose
  have hδ₁ : IsDeformationClassMap (SmoothProperCurve.baseChange R c K)
      (SmoothProperCurve.sectionBaseChange K ε) K (𝒲.pullback c K) δ₁ := hdeformationMap.choose_spec
  have hT1 := fun m => apply_baseTransport_eq_H1baseChangeMap c ε K 𝒲 hδ hδ₁ m
  have hbx : RigKerDualNumber.baseTransport K c ε K (h.kerPointsToRigKer K x) =
    h'.kerPointsToRigKer K x₁ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport c ε D h K h' hP K
      x x₁ hx₁
  have hbxr : RigKerDualNumber.baseTransport K c ε K (h.kerPointsToRigKer K xr) =
    h'.kerPointsToRigKer K xr₁ :=
    AlgebraicGeometry.RelPicard.RigKerDualNumber.kerPointsToRigKer_baseTransport c ε D h K h' hP K
      xr xr₁ hxr₁
  have hs₁ : δ₁ (h'.kerPointsToRigKer K x₁) =
      Submodule.Quotient.mk ((HomOver.baseChange (𝒲.pullback c K) (pullback.snd c (specMap R K))
        K).map01 s) := by
    rw [← hbx, hT1, hs]; rfl
  have hKK : specMap K K = 𝟙 (Spec (.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have : IsIso (specMap K K) := by rw [hKK]; infer_instance
  have : IsIntegral (Limits.pullback (pullback.snd c (specMap R K)) (specMap K K)) :=
    IsIntegral.of_isIso (inv (pullback.fst (pullback.snd c (specMap R K)) (specMap K K)))
  refine AlgebraicCurve.cechH1ToH1_corrH1_of_pullback_specMap_self K (pullback.snd c (specMap R K))
    (𝒲.pullback c K) y
    (pullback.lift πα y Hα) (pullback.lift πβ y Hβ) (pullback.lift_snd _ _ _) (pullback.lift_snd _
      _ _)
    (pullback.lift (pullback.lift πα y Hα) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
    (pullback.lift (pullback.lift πβ y Hβ) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)
    s (δ (h.kerPointsToRigKer K xr)) ?_ φα φβ hφπα hφπβ hφα hφβ htrα hW hsr
  intro instNE₁ ψα ψβ hψπα hψπβ hψα hψβ htrψα hW₁ hs₁m
  have hfieldResult :=
    exists_cechH1ToH1_germ_eq_traceAlong_of_classifies_normModule_pullback_of_field
      K (pullback.snd c (specMap R K)) (SmoothProperCurve.sectionBaseChange K ε) hC (D.baseChange
        K) h' y
      (pullback.lift πα y Hα) (pullback.lift πβ y Hβ) Hα₁ Hβ₁ d hd
      (pullback.lift (pullback.lift πα y Hα) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
      (pullback.lift (pullback.lift πβ y Hβ) y (by rw [pullback.lift_snd, hKK, Category.comp_id]))
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _)
      φ₁K hmoduli₁ (𝒲.pullback c K) hδ₁ x₁ xr₁ hxr₁' _ hs₁ ψα ψβ hψπα hψπβ hψα hψβ htrψα hW₁ hs₁m
  let sr₁ : (((𝒲.pullback c K).pullback (pullback.snd c (specMap R K)) K).cover
      (pullback.snd (pullback.snd c (specMap R K)) (specMap K K))).A01 := hfieldResult.choose
  have hsrr₁ := hfieldResult.choose_spec.choose
  let x₁' := hfieldResult.choose_spec.choose_spec.choose
  have hfieldClauses := hfieldResult.choose_spec.choose_spec.choose_spec
  have h1 := hfieldClauses.1
  have h2 := hfieldClauses.2.1
  have h3 := hfieldClauses.2.2
  refine ⟨sr₁, hsrr₁, x₁', ?_, h2, h3⟩
  rw [← h1, ← hbxr, hT1]
end AlgebraicGeometry.RelPicard.IsDeformationClassMap
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelPicard.RigKerDualNumber.baseTransport_mk
  AlgebraicGeometry.RelPicard.BaseTransport.idOver_coe
  AlgebraicGeometry.RelPicard.RigKerDualNumber.baseTransport_symm_mk
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U0
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.preimage_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.ofPreimage_hom
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

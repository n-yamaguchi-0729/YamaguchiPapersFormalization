/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_classifies_rigidify_normModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_normModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_normModule_unit_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_normModule_tensor_iso
import Nyll.JacobianVarieties.Picard.FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_finrank_pullbackMap_of_comp_eq

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Multiplicativity of the represented norm map

Compare classification of tensor products and units under the norm transform.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.NormMultiplication
attribute [-instance]
  TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
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
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

noncomputable section

namespace P2mNormHomCrux

section CurveChange

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (π : C' ⟶ C) (hπ : π ≫ c = c')

theorem isFinite_curveChange [IsFinite π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite π› (inferInstance : IsFinite (𝟙 T))
    hπ.symm
    (Category.id_comp t).symm

theorem flat_curveChange [Flat π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Flat (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @Flat) ‹Flat π› (inferInstance : Flat (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation π] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : LocallyOfFinitePresentation (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) ‹LocallyOfFinitePresentation π›
    (inferInstance : LocallyOfFinitePresentation (𝟙 T)) hπ.symm (Category.id_comp t).symm

theorem finrank_curveChange [Flat π] [IsFinite π] {d : ℕ} (hd : ∀ y : C, π.finrank y = d)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∀ y, (curveChange π hπ t).finrank y = d :=
  fun y => (Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t π hπ y).trans (hd _)

end CurveChange

section Transform

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (π : C' ⟶ C) (hπ : π ≫ c = c')
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (d : ℕ) (hd : ∀ y : C, π.finrank y = d)

include hd

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange π hπ t) d M.L) :=
  have := isFinite_curveChange π hπ t
  have := flat_curveChange π hπ t
  have := locallyOfFinitePresentation_curveChange π hπ t
  Scheme.Modules.IsInvertible.normModule _ d (finrank_curveChange π hπ hd t) M.isInvertible

/-- The rigidified line bundle obtained by applying the norm. -/
def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    RigidifiedLineBundle c ε t :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    (Scheme.Modules.normModule (curveChange π hπ t) d M.L) (hinv π hπ d hd t M)

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
    :
    (Phi (ε := ε) π hπ d hd t M).L =
      (RigidifiedLineBundle.ofInvertible (ε := ε)
        (Scheme.Modules.normModule (curveChange π hπ t) d M.L) (hinv π hπ d hd t M)).L := rfl

theorem hcongr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c' ε' t)
    (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi (ε := ε) π hπ d hd t M).L ≅ (Phi (ε := ε) π hπ d hd t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.normModuleMapIso _ d h.some)

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε := ε) π hπ d hd t M) :=
  FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange (ε := ε) π hπ d hd M.L M.isInvertible
    (fun k _ _ s => hM k s) (hinv π hπ d hd t M)

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε := ε) π hπ d hd t (RigidifiedLineBundle.unit (c := c') (ε := ε') t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  have := isFinite_curveChange π hπ t
  have := flat_curveChange π hπ t
  have := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨eN⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t)
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv π hπ d hd t (RigidifiedLineBundle.unit t))
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t).isInvertible eN
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t)
  exact ⟨e1 ≪≫ e2⟩

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M M' : RigidifiedLineBundle c' ε' t) :
    Nonempty ((Phi (ε := ε) π hπ d hd t (M.tensor M')).L ≅
      ((Phi (ε := ε) π hπ d hd t M).tensor (Phi (ε := ε) π hπ d hd t M')).L) := by
  have := isFinite_curveChange π hπ t
  have := flat_curveChange π hπ t
  have := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨eT⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t) _ _ M.isInvertible M'.isInvertible
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv π hπ d hd t (M.tensor M')) ((hinv π hπ d hd t M).tensor (hinv π hπ d hd t M')) eT
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε)
    (hinv π hπ d hd t M) (hinv π hπ d hd t M')
  exact ⟨e1 ≪≫ e2⟩

end Transform

end P2mNormHomCrux

end

end JacobianVarieties.Picard.Proofs.NormMultiplication

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian

universe u

open _root_.JacobianVarieties.Picard.Proofs in
open NormMultiplication.P2mNormHomCrux in
theorem RepresentsRelSubPic.comp_mul_eq_mul_comp_of_classifies_rigidify_normModule
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : C, π.finrank x = d)
    (N : SchemeHomOver D'.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D'.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange π hπ t) d (h'.poincare.pullbackAlong a).L))) :
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D'.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t x y)
              N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      D'.zeroSection ≫ N.1 = D.zeroSection := by
  have hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
      (hM : (algEquivZeroCut c' ε').P t M),
      postComp N (h'.classify t M hM) =
        h.classify t (Phi (ε := ε) π hπ d hd t M) (hcut (ε := ε) π hπ d hd t M hM) := by
    intro T t M hM
    apply h.classify_unique
    obtain ⟨e1⟩ := hN t (h'.classify t M hM)
    obtain ⟨e2⟩ := h'.classify_spec t M hM
    exact ⟨e1 ≪≫ Scheme.Modules.rigidifyMapIso _ _ (Scheme.Modules.normModuleMapIso _ d e2)⟩
  have hhom := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut c ε) (P' := algEquivZeroGroupCut c' ε') h h' (Phi (ε := ε) π hπ d hd)
    (fun t M hM => hcut (ε := ε) π hπ d hd t M hM) (fun t M M' => htensor (ε := ε) π hπ d hd t M M')
    (fun t => hunit (ε := ε) π hπ d hd t) N (fun t M hM => hφ t M hM)
  exact ⟨fun t x y => hhom.1 t x y, hhom.2⟩
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply

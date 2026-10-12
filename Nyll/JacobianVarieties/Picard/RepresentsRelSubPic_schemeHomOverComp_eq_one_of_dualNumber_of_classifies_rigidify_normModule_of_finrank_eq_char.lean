/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_eq_one_of_dualNumber_of_classifies_rigidify_normModule_of_finrank_eq_char.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.EqToHom
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.JacobianVarieties.Picard.nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_pullbackAlong_one_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints

/-! The norm map kills tangent points under the characteristic-rank hypothesis. -/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DualNumberNormTriviality
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.HomOver.mk.injEq
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace NFDUNIT

private theorem specMap_self (κ : Type u) [CommRing κ] :
    Scheme.TwoAffineOpenCover.specMap κ κ = 𝟙 (Spec (CommRingCat.of κ)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap κ κ)) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

end NFDUNIT
end JacobianVarieties.Picard.Proofs.DualNumberNormTriviality

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.JacobianVarieties.Picard.Proofs.DualNumberNormTriviality
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
universe u

/-- The norm map kills tangent points under the characteristic-rank hypothesis. -/
theorem schemeHomOverComp_eq_one_of_dualNumber_of_classifies_rigidify_normModule_of_finrank_eq_char
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {C C' : Scheme.{u}} [IsIntegral C] [IsIntegral C']
    {c : C ⟶ Spec (CommRingCat.of κ)} {c' : C' ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType c] (𝒱 : C.TwoAffineOpenCover)
    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) c} {ε' : SchemeHomOver (𝟙 (Spec
      (CommRingCat.of κ))) c'}
    {D : RelativePic0Designation κ c} {D' : RelativePic0Designation κ c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε'
      (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hd : ∀ x : C, π.finrank x = p)
    (hinj : ∀ x₁ x₂ : C', IsClosed ({x₁} : Set C') → IsClosed ({x₂} : Set C') → π.base x₁ = π.base
      x₂ → x₁ = x₂)
    (N : SchemeHomOver D'.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t D'.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange π hπ t) p (h'.poincare.pullbackAlong a).L)))
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) D'.toBase)
    (hu : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ u.1 =
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').one (𝟙 _)).1) :
    NeronModelInfra.schemeHomOverComp u N =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
        (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) := by
  classical
  let law' : RelativeGroupLaw κ D'.toBase := RepresentsRelSubPic.relativeGroupLaw (P :=
    algEquivZeroGroupCut c' ε') h'
  let red : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap κ κ)
      (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ)) := dualNumberReductionOver κ κ
  have hone : (law'.one (Scheme.TwoAffineOpenCover.specMap κ κ)).1 = (law'.one (𝟙 _)).1 := by
    have hψ : 𝟙 (Spec (CommRingCat.of κ)) ≫ 𝟙 (Spec (CommRingCat.of κ)) =
        Scheme.TwoAffineOpenCover.specMap κ κ := by
      rw [Category.comp_id, NFDUNIT.specMap_self]
    have := congrArg Subtype.val (law'.one_natural (𝟙 _) (Scheme.TwoAffineOpenCover.specMap κ κ) (𝟙
      _) hψ)
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at this
    exact this.symm
  have hredu : postComp u red = law'.one (Scheme.TwoAffineOpenCover.specMap κ κ) := by
    apply Subtype.ext
    change dualNumberReduction κ κ ≫ u.1 = (law'.one (Scheme.TwoAffineOpenCover.specMap κ κ)).1
    rw [hone]
    exact hu
  have h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c' (dualNumberReductionOver
    κ κ))).obj
      (h'.poincare.pullbackAlong u).L ≅
        SheafOfModules.unit.{u} (pullback c' (Scheme.TwoAffineOpenCover.specMap κ κ)).ringCatSheaf)
          := by
    obtain ⟨e⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c'
      ε') h'
      (Scheme.TwoAffineOpenCover.specMap κ κ)
    exact ⟨RigidifiedLineBundle.pullbackAlongPullbackAlongIso' h'.poincare u red ≪≫
      eqToIso (congrArg (fun ψ => (h'.poincare.pullbackAlong ψ).L) hredu) ≪≫ e⟩
  obtain ⟨eN⟩ :=
    nonempty_normModule_curveChange_dualNumber_iso_unit_of_finrank_eq_char_of_forall_isClosed_eq
      c c' 𝒱 hC π hπ hd hinj (h'.poincare.pullbackAlong u).L (h'.poincare.pullbackAlong
        u).isInvertible h0
  obtain ⟨eR⟩ :=
    AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
    (rigSection c (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ)) ε)
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ)))
    (SheafOfModules.unit.{u} (pullback c (Scheme.TwoAffineOpenCover.specMap κ (DualNumber
      κ))).ringCatSheaf)
    ⟨Scheme.Modules.pullbackUnitIso _⟩
  obtain ⟨e1⟩ := hN _ u
  obtain ⟨e5⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c ε)
    h
    (Scheme.TwoAffineOpenCover.specMap κ (DualNumber κ))
  apply h.ext_of_iso
  exact ⟨e1 ≪≫ Scheme.Modules.rigidifyMapIso _ _ eN ≪≫ eR ≪≫ e5.symm⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.RelPicard.RigKerDualNumber.setoid
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
  SheafOfModules.isIso_ihomModelToIhom

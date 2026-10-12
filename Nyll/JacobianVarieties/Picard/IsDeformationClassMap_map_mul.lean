/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_map_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Tactic.LinearCombination
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.JacobianVarieties.Picard.RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_tensorSections

/-!
# Compatibility of deformation classes with tensor multiplication.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationMultiplication
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

/-- The deformation class of a tensor product is the sum of the deformation classes. -/
theorem _root_.AlgebraicGeometry.RelPicard.IsDeformationClassMap.map_mul
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c}
    {A : Type u} [CommRing A] [Algebra R A] {𝒱 : C.TwoAffineOpenCover}
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ)
    (x y : RigKerDualNumber c ε A) :
    δ (RigKerDualNumber.mul c ε A x y) = δ x + δ y := by
  induction x using Quotient.ind with
  | _ M =>
  induction y using Quotient.ind with
  | _ N =>
  obtain ⟨e₀, e₁, f, h₀, h₁, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 M
  obtain ⟨e₀', e₁', f', h₀', h₁', hN⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 N
  rw [hδ M e₀ e₁ f h₀ h₁ hM, hδ N e₀' e₁' f' h₀' h₁' hN]
  have h := hδ ⟨M.1.tensor N.1, RigKerDualNumber.tensor_mem c ε A M N⟩
    (Scheme.Modules.tensorSections e₀ e₀') (Scheme.Modules.tensorSections e₁ e₁') (f + f')
    (h₀.tensorSections h₀') (h₁.tensorSections h₁') ?_
  · rw [← Submodule.Quotient.mk_add, ← h]
    rfl
  · change (M.1.L ⊗ N.1.L).presheaf.map (homOfLE _).op (Scheme.Modules.tensorSections e₁ e₁') =
        _ • (M.1.L ⊗ N.1.L).presheaf.map (homOfLE _).op (Scheme.Modules.tensorSections e₀ e₀')
    rw [Scheme.Modules.map_homOfLE_tensorSections, Scheme.Modules.map_homOfLE_tensorSections, hM,
      hN,
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right, smul_smul]
    congr 1
    change oneAddEpsMul A 𝒱 c f * oneAddEpsMul A 𝒱 c f' = oneAddEpsMul A 𝒱 c (f + f')
    simp only [oneAddEpsMul, map_add]
    have he : algebraMap (DualNumber A)
        ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01
          DualNumber.eps *
        algebraMap (DualNumber A) _ DualNumber.eps = 0 := by
      rw [← _root_.map_mul, DualNumber.eps_mul_eps, _root_.map_zero]
    linear_combination ((dualNumberThickening A 𝒱 c).map01 f * (dualNumberThickening A 𝒱 c).map01
      f') * he
end JacobianVarieties.Picard.Proofs.DeformationMultiplication
end ProofImplementation

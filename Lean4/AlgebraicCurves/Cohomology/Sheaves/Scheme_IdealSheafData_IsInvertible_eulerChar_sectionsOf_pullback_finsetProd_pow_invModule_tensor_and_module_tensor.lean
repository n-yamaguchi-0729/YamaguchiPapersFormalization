/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
import AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul

/-!
# Scheme Ideal Sheaf Data Is Invertible euler Char sections Of pullback finset Prod pow inv
Module tensor and module tensor
-/

section ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible (
  eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul)
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible (
  eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul)

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicFinsetProduct
attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom
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
  ProjSpaceCech.GradedModule.H.module
attribute [-instance] ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
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
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

universe u v


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.IdealSheafData.one_eq_top IsProper Scheme.Modules.pullback
  IsFinite Spec Scheme Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData
  Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top
  Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.Modules.IsInvertible
  Scheme.TwoAffineOpenCover Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor
  Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul)

namespace FinsetProdTwistChi

open _root_.AlgebraicGeometry


variable {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
  (𝒲 : Y.TwoAffineOpenCover)

/-- The difference between the dimensions of degree-zero and degree-one Cech cohomology. -/
def chi (M : Y.Modules) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1

theorem chi_def (M : Y.Modules) :
    chi y 𝒲 M = (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y
      M).H1 :=
  rfl

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem chi_congr {M M' : Y.Modules} (e : M ≅ M') : chi y 𝒲 M = chi y 𝒲 M' := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y)
      (Category.id_comp y)
      𝒲 M' M (e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm)
  obtain rfl : 𝒱₂ = 𝒲 := cover_ext h0 h1
  rw [chi_def, chi_def, e0.finrank_eq, e1.finrank_eq]

theorem nonempty_iso_unit_of_iso_tensor_self {C : Type*} [Category C] [MonoidalCategory C] {E E' :
  C}
    (e : E ≅ E ⊗ E) (d : E ⊗ E' ≅ 𝟙_ C) : Nonempty (E ≅ 𝟙_ C) :=
  ⟨(ρ_ E).symm ≪≫ whiskerLeftIso E d.symm ≪≫ (α_ E E E').symm ≪≫ whiskerRightIso e.symm E' ≪≫ d⟩

theorem nonempty_invModule_one_iso (X : Scheme.{u}) :
    Nonempty ((1 : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) := by
  have h1 : (1 : X.IdealSheafData).IsInvertible := by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor h1 h1
  exact nonempty_iso_unit_of_iso_tensor_self
    (eqToIso (congrArg Scheme.IdealSheafData.invModule (one_mul (1 : X.IdealSheafData)).symm) ≪≫ em)
    (h1.isInvertible_invModule.dual).2.some

theorem nonempty_module_one_iso (X : Scheme.{u}) :
    Nonempty ((1 : X.IdealSheafData).module ≅ 𝟙_ X.Modules) := by
  have h1 : (1 : X.IdealSheafData).IsInvertible := by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor h1 h1
  exact nonempty_iso_unit_of_iso_tensor_self
    (eqToIso (congrArg Scheme.IdealSheafData.module (one_mul (1 : X.IdealSheafData)).symm) ≪≫ em)
    (h1.isInvertible_module.dual).2.some

variable {X : Scheme.{u}} (ι : Y ⟶ X) [IsProper y] {F : Type v} [DecidableEq F] (I : F →
  X.IdealSheafData) (a : F → ℕ) (d : F → ℕ)

omit [DecidableEq F] in
theorem isInvertible_finsetProd (S : Finset F) (hI : ∀ i ∈ S, (I i).IsInvertible) :
    (∏ i ∈ S, I i ^ a i).IsInvertible := by
  refine Finset.prod_induction _ (fun J : X.IdealSheafData => J.IsInvertible)
    (fun _ _ h h' => h.mul h') ?_ (fun i hi => (hI i hi).pow (a i))
  rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top

omit [DecidableEq F] in
theorem main : ∀ (S : Finset F), (∀ i ∈ S, (I i).IsInvertible) → (∀ i ∈ S, ((I i).comap
  ι).IsInvertible) →
    (∀ i ∈ S, IsFinite (((I i).comap ι).subschemeι ≫ y)) →
    (∀ i ∈ S, ∀ t : Spec (CommRingCat.of k), (((I i).comap ι).subschemeι ≫ y).finrank t = d i) →
    ∀ (M : X.Modules), Scheme.Modules.IsInvertible M →
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).invModule ⊗ M)) =
          chi y 𝒲 ((Scheme.Modules.pullback ι).obj M) + ∑ i ∈ S, (a i : ℤ) * (d i : ℤ) ∧
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a i).module ⊗ M)) =
          chi y 𝒲 ((Scheme.Modules.pullback ι).obj M) - ∑ i ∈ S, (a i : ℤ) * (d i : ℤ) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ _ _ M hM
    obtain ⟨e1⟩ := nonempty_invModule_one_iso X
    obtain ⟨e2⟩ := nonempty_module_one_iso X
    simp only [Finset.prod_empty, Finset.sum_empty, add_zero, sub_zero]
    exact ⟨chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso e1 M ≪≫ λ_ M)),
      chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso e2 M ≪≫ λ_ M))⟩
  | insert i₀ S hi₀ ih =>
    intro hI hIY hZ hdeg M hM
    have hI' : ∀ i ∈ S, (I i).IsInvertible := fun i hi => hI i (Finset.mem_insert_of_mem hi)
    have hIY' : ∀ i ∈ S, ((I i).comap ι).IsInvertible := fun i hi => hIY i
      (Finset.mem_insert_of_mem hi)
    have hZ' : ∀ i ∈ S, IsFinite (((I i).comap ι).subschemeι ≫ y) := fun i hi => hZ i
      (Finset.mem_insert_of_mem hi)
    have hdeg' : ∀ i ∈ S, ∀ t : Spec (CommRingCat.of k), (((I i).comap ι).subschemeι ≫ y).finrank t
      = d i :=
      fun i hi => hdeg i (Finset.mem_insert_of_mem hi)
    have h0 : (I i₀).IsInvertible := hI i₀ (Finset.mem_insert_self _ _)
    have hP : (∏ i ∈ S, I i ^ a i).IsInvertible := isInvertible_finsetProd I a S hI'
    rw [Finset.prod_insert hi₀, Finset.sum_insert hi₀]
    obtain ⟨einv⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor (h0.pow
      (a i₀)) hP
    obtain ⟨emod⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor (h0.pow (a
      i₀)) hP
    have hPinvM : Scheme.Modules.IsInvertible ((∏ i ∈ S, I i ^ a i).invModule ⊗ M) :=
      hP.isInvertible_invModule.tensor hM
    have hPmodM : Scheme.Modules.IsInvertible ((∏ i ∈ S, I i ^ a i).module ⊗ M) :=
      hP.isInvertible_module.tensor hM
    obtain ⟨ih1, ih2⟩ := ih hI' hIY' hZ' hdeg' M hM
    constructor
    · rw [chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso einv M ≪≫ α_ _ _ _))]
      have h1 := eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
        ι y h0 (hIY i₀ (Finset.mem_insert_self _ _)) (hZ i₀ (Finset.mem_insert_self _ _))
        (hdeg i₀ (Finset.mem_insert_self _ _)) _ hPinvM (a i₀) 𝒲
      rw [← chi_def, ← chi_def] at h1
      rw [h1, ih1]; ring
    · rw [chi_congr y 𝒲 ((Scheme.Modules.pullback ι).mapIso (whiskerRightIso emod M ≪≫ α_ _ _ _))]
      have h2 := eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
        ι y h0 (hIY i₀ (Finset.mem_insert_self _ _)) (hZ i₀ (Finset.mem_insert_self _ _))
        (hdeg i₀ (Finset.mem_insert_self _ _)) _ hPmodM (a i₀) 𝒲
      rw [← chi_def, ← chi_def] at h2
      rw [h2, ih2]; ring

end AlgebraicGeometry.FinsetProdTwistChi

end
end AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicFinsetProduct

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicFinsetProduct
universe u v
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem eulerChar_sectionsOf_pullback_finsetProd_pow_invModule_tensor_and_module_tensor
    {k : Type u} [Field k] {X Y : Scheme.{u}} (ι : Y ⟶ X) (y : Y ⟶ Spec (CommRingCat.of k))
      [IsProper y]
    {F : Type v} (S : Finset F) (I : F → X.IdealSheafData) (a d : F → ℕ)
    (hI : ∀ i ∈ S, (I i).IsInvertible) (hIY : ∀ i ∈ S, ((I i).comap ι).IsInvertible)
    (hZ : ∀ i ∈ S, IsFinite (((I i).comap ι).subschemeι ≫ y))
    (hdeg : ∀ i ∈ S, ∀ t : Spec (CommRingCat.of k), (((I i).comap ι).subschemeι ≫ y).finrank t = d
      i)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒲 : Y.TwoAffineOpenCover) :
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a
      i).invModule ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a
          i).invModule ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H1
        + ∑ i ∈ S, (a i : ℤ) * (d i : ℤ)) ∧
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a
      i).module ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((∏ i ∈ S, I i ^ a
          i).module ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H1
        - ∑ i ∈ S, (a i : ℤ) * (d i : ℤ)) := by
  classical
  have h := AlgebraicGeometry.FinsetProdTwistChi.main y 𝒲 ι I a d S hI hIY hZ hdeg M hM
  simp only [AlgebraicGeometry.FinsetProdTwistChi.chi_def] at h
  exact h
end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
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
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  isScalarTower
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instLinearOrder
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  module
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instFintype
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  addCommGroup
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instDecidableEqIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  moduleSections
open _root_.SheafOfModules in
attribute [-instance]
  isIso_ihomModelToIhom
open AlgebraicGeometry.Scheme.OrderedAffineCoverOf in
attribute [-instance]
  instDecidableEqIdx
  instFintype
  instLinearOrder
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  instSubsingletonObjZero
open AlgebraicGeometry.OModulePresheaf.Leray in
attribute [-instance]
  relAltC_scalarTower
  ker_relAltd_modΓ
  relAltC_modΓ
  biC_abGrp
  relAltH_modΓ
  ker_relAltd_smul
  relAltH_scalarTower
  relAltH_smul
  biC_module
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffHom.id_app
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
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
attribute [-simp] ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

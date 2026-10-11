/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

/-!
# Scheme Ideal Sheaf Data Is Invertible euler Char sections Of pullback pow inv Module
tensor eq add mul
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicInversePower
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

universe u


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
  Scheme.TwoAffineOpenCover Scheme.Modules.pullbackTensorObjIso
  Scheme.Modules.pullbackTensorUnitObjIso
  Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor
  Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor
  Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso)

namespace PullbackPowTwist

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

variable {X : Scheme.{u}} (ι : Y ⟶ X) [IsProper y]

theorem chi_tensor_pullback_invModule {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hK : (I.comap ι).IsInvertible) {d : ℕ} (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ q : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank q = d)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L) :
    chi y 𝒲 (L ⊗ (Scheme.Modules.pullback ι).obj I.invModule) = chi y 𝒲 L + d := by
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso ι hI hK
  rw [chi_congr y 𝒲 (whiskerLeftIso L e), chi_def, chi_def]
  exact Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq y hK hZ hdeg L
    hL 𝒲

theorem nonempty_pullback_module_tensor_pullback_invModule_iso {I : X.IdealSheafData} (hI :
  I.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback ι).obj I.module ⊗ (Scheme.Modules.pullback ι).obj
      I.invModule ≅
      𝟙_ Y.Modules) := by
  have eX : I.module ⊗ I.invModule ≅ 𝟙_ X.Modules := (hI.isInvertible_module.dual).2.some
  exact ⟨(Scheme.Modules.pullbackTensorObjIso ι I.module I.invModule).symm ≪≫
    (Scheme.Modules.pullback ι).mapIso eX ≪≫ Scheme.Modules.pullbackTensorUnitObjIso ι⟩

theorem chi_tensor_pullback_module {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hK : (I.comap ι).IsInvertible) {d : ℕ} (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ q : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank q = d)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L) :
    chi y 𝒲 (L ⊗ (Scheme.Modules.pullback ι).obj I.module) = chi y 𝒲 L - d := by
  have hA : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ι).obj I.module) :=
    hI.isInvertible_module.pullback ι
  obtain ⟨eAB⟩ := nonempty_pullback_module_tensor_pullback_invModule_iso ι hI
  have h := chi_tensor_pullback_invModule y 𝒲 ι hI hK hZ hdeg
    (L ⊗ (Scheme.Modules.pullback ι).obj I.module) (hL.tensor hA)
  rw [chi_congr y 𝒲 (α_ _ _ _ ≪≫ whiskerLeftIso L eAB ≪≫ ρ_ L)] at h
  omega

theorem chi_tensor_pullback_invModule_pow {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hK : (I.comap ι).IsInvertible) {d : ℕ} (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ q : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank q = d) (a : ℕ) :
    ∀ (L : Y.Modules), Scheme.Modules.IsInvertible L →
      chi y 𝒲 (L ⊗ (Scheme.Modules.pullback ι).obj ((I ^ a).invModule)) = chi y 𝒲 L + a * d := by
  induction a with
  | zero =>
    intro L hL
    obtain ⟨e1⟩ := nonempty_invModule_one_iso X
    rw [pow_zero, chi_congr y 𝒲 (whiskerLeftIso L ((Scheme.Modules.pullback ι).mapIso e1 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso ι) ≪≫ ρ_ L)]
    simp
  | succ a ih =>
    intro L hL
    obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor (hI.pow a)
      hI
    have hBa : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ι).obj ((I ^ a).invModule)) :=
      (hI.pow a).isInvertible_invModule.pullback ι
    rw [pow_succ, chi_congr y 𝒲 (whiskerLeftIso L ((Scheme.Modules.pullback ι).mapIso em ≪≫
        Scheme.Modules.pullbackTensorObjIso ι _ _) ≪≫ (α_ _ _ _).symm),
      chi_tensor_pullback_invModule y 𝒲 ι hI hK hZ hdeg _ (hL.tensor hBa), ih L hL]
    push_cast
    ring

theorem chi_tensor_pullback_module_pow {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hK : (I.comap ι).IsInvertible) {d : ℕ} (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ q : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank q = d) (b : ℕ) :
    ∀ (L : Y.Modules), Scheme.Modules.IsInvertible L →
      chi y 𝒲 (L ⊗ (Scheme.Modules.pullback ι).obj ((I ^ b).module)) = chi y 𝒲 L - b * d := by
  induction b with
  | zero =>
    intro L hL
    obtain ⟨e1⟩ := nonempty_module_one_iso X
    rw [pow_zero, chi_congr y 𝒲 (whiskerLeftIso L ((Scheme.Modules.pullback ι).mapIso e1 ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso ι) ≪≫ ρ_ L)]
    simp
  | succ b ih =>
    intro L hL
    obtain ⟨em⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor (hI.pow b) hI
    have hAb : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ι).obj ((I ^ b).module)) :=
      (hI.pow b).isInvertible_module.pullback ι
    rw [pow_succ, chi_congr y 𝒲 (whiskerLeftIso L ((Scheme.Modules.pullback ι).mapIso em ≪≫
        Scheme.Modules.pullbackTensorObjIso ι _ _) ≪≫ (α_ _ _ _).symm),
      chi_tensor_pullback_module y 𝒲 ι hI hK hZ hdeg _ (hL.tensor hAb), ih L hL]
    push_cast
    ring

theorem chi_pullback_invModule_pow_tensor {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hK : (I.comap ι).IsInvertible) {d : ℕ} (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ q : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank q = d) (a : ℕ)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    chi y 𝒲 ((Scheme.Modules.pullback ι).obj ((I ^ a).invModule ⊗ M)) =
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj M) + a * d := by
  rw [chi_congr y 𝒲 (Scheme.Modules.pullbackTensorObjIso ι _ _ ≪≫ β_ _ _),
    chi_tensor_pullback_invModule_pow y 𝒲 ι hI hK hZ hdeg a _ (hM.pullback ι)]

theorem chi_pullback_module_pow_tensor {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hK : (I.comap ι).IsInvertible) {d : ℕ} (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ q : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank q = d) (b : ℕ)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    chi y 𝒲 ((Scheme.Modules.pullback ι).obj ((I ^ b).module ⊗ M)) =
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj M) - b * d := by
  rw [chi_congr y 𝒲 (Scheme.Modules.pullbackTensorObjIso ι _ _ ≪≫ β_ _ _),
    chi_tensor_pullback_module_pow y 𝒲 ι hI hK hZ hdeg b _ (hM.pullback ι)]

end AlgebraicGeometry.PullbackPowTwist

end
end AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicInversePower

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicInversePower
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
    {k : Type u} [Field k] {X Y : Scheme.{u}} (ι : Y ⟶ X) (y : Y ⟶ Spec (CommRingCat.of k))
      [IsProper y]
    {I : X.IdealSheafData} (hI : I.IsInvertible) (hIY : (I.comap ι).IsInvertible) {d : ℕ}
    (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ t : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank t = d)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (r : ℕ) (𝒲 : Y.TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((I ^ r).invModule ⊗ M))).H0
      : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((I ^ r).invModule ⊗
          M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H1 + r * d := by
  rw [← AlgebraicGeometry.PullbackPowTwist.chi_def, ← AlgebraicGeometry.PullbackPowTwist.chi_def]
  exact AlgebraicGeometry.PullbackPowTwist.chi_pullback_invModule_pow_tensor y 𝒲 ι hI hIY hZ hdeg r
    M hM
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

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_foldr_pow_invModule_tensor_pow_module_tensor_eq_add_sum.lean
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
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul

/-!
# Scheme Ideal Sheaf Data Is Invertible euler Char sections Of pullback foldr pow inv Module
tensor pow module tensor eq add sum
-/

section ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible (
  eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul)

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicFoldProduct
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
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
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

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (IsProper Scheme.Modules.pullback IsFinite Spec Scheme
  Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.IdealSheafData.IsInvertible
  Scheme.Modules.IsInvertible Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
  Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul)

namespace FoldrTwistChi

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

variable {X : Scheme.{u}} (ι : Y ⟶ X) [IsProper y]
  {m : ℕ} (I : Fin m → X.IdealSheafData) (hI : ∀ j, (I j).IsInvertible) (pos neg : Fin m → ℕ)

include hI in
theorem isInvertible_foldr (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) :
    ∀ l : List (Fin m), Scheme.Modules.IsInvertible
      (l.foldr (fun j M => ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module ⊗ M) N)
  | [] => by simpa using hN
  | j :: l => by
    simp only [List.foldr_cons]
    exact ((hI j).pow (pos j)).isInvertible_invModule.tensor
      (((hI j).pow (neg j)).isInvertible_module.tensor (isInvertible_foldr N hN l))
include hI in
theorem chi_pullback_foldr (hIY : ∀ j, ((I j).comap ι).IsInvertible) (d : Fin m → ℕ)
    (hZ : ∀ j, IsFinite (((I j).comap ι).subschemeι ≫ y))
    (hdeg : ∀ j (t : Spec (CommRingCat.of k)), (((I j).comap ι).subschemeι ≫ y).finrank t = d j)
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) :
    ∀ l : List (Fin m),
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj
        (l.foldr (fun j M => ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module ⊗ M) N)) =
      chi y 𝒲 ((Scheme.Modules.pullback ι).obj N) + (l.map fun j => ((pos j : ℤ) - (neg j : ℤ)) *
        (d j : ℤ)).sum
  | [] => by simp
  | j :: l => by
    have ih := chi_pullback_foldr hIY d hZ hdeg N hN l
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have hR := isInvertible_foldr I hI pos neg N hN l
    have hmid : Scheme.Modules.IsInvertible (((I j) ^ (neg j)).module ⊗
        l.foldr (fun j M => ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module ⊗ M) N) :=
      ((hI j).pow (neg j)).isInvertible_module.tensor hR
    have h1 := eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
      ι y (hI j) (hIY j) (hZ j) (hdeg j) _ hmid (pos j) 𝒲
    have h2 :=
      Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
      ι y (hI j) (hIY j) (hZ j) (hdeg j) _ hR (neg j) 𝒲
    rw [← chi_def, ← chi_def] at h1 h2
    rw [h1, h2, ih]
    ring

end AlgebraicGeometry.FoldrTwistChi

end
end AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicFoldProduct

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicFoldProduct
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem eulerChar_sectionsOf_pullback_foldr_pow_invModule_tensor_pow_module_tensor_eq_add_sum
    {k : Type u} [Field k] {X Y : Scheme.{u}} (ι : Y ⟶ X) (y : Y ⟶ Spec (CommRingCat.of k))
      [IsProper y]
    {m : ℕ} (I : Fin m → X.IdealSheafData) (hI : ∀ j, (I j).IsInvertible) (hIY : ∀ j, ((I j).comap
      ι).IsInvertible)
    (d : Fin m → ℕ) (hZ : ∀ j, IsFinite (((I j).comap ι).subschemeι ≫ y))
    (hdeg : ∀ j (t : Spec (CommRingCat.of k)), (((I j).comap ι).subschemeι ≫ y).finrank t = d j)
    (pos neg : Fin m → ℕ) (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) (𝒲 :
      Y.TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj
        ((List.finRange m).foldr (fun j M => ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module
          ⊗ M) N))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj
        ((List.finRange m).foldr (fun j M => ((I j) ^ (pos j)).invModule ⊗ ((I j) ^ (neg j)).module
          ⊗ M) N))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj N)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj N)).H1
        + ∑ j, ((pos j : ℤ) - (neg j : ℤ)) * (d j : ℤ) := by
  have h := AlgebraicGeometry.FoldrTwistChi.chi_pullback_foldr y 𝒲 ι I hI pos neg hIY d hZ hdeg N
    hN (List.finRange m)
  rw [AlgebraicGeometry.FoldrTwistChi.chi_def, AlgebraicGeometry.FoldrTwistChi.chi_def] at h
  rw [h, ← List.ofFn_eq_map, List.sum_ofFn]
end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
end ProofImplementation

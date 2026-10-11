/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_range_moduleIota_app_and_injective
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ofUnitSection_sectionDual_app

/-!
# The zero scheme of the inverse-ideal section

The canonical section of the inverse module of an invertible ideal sheaf has
zero-scheme ideal equal to the original ideal sheaf.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
open
  _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

universe v u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

noncomputable section

namespace ZeroSchemeCanonMC

open _root_.CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- The canonical map to the internal-Hom bidual, obtained by currying the braided evaluation
    map. -/
def toBidual (M : C) : M ⟶ (ihom ((ihom M).obj (𝟙_ C))).obj (𝟙_ C) :=
  MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))

omit [BraidedCategory C] in
theorem unitIsoSelf_inv (X : C) :
    (MonoidalClosed.unitIsoSelf X).inv = MonoidalClosed.curry (λ_ X).hom := by
  have h := unit_conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  dsimp at h
  erw [Category.id_comp] at h
  change (conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom).app X = _
  rw [h, MonoidalClosed.curry_eq]
  try rfl

theorem toBidual_comp_pre_app_comp_unitIsoSelf_hom {M : C} (ι : M ⟶ 𝟙_ C) :
    toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ C)).hom = ι := by
  have hk : MonoidalClosed.uncurry
      (toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C)) = (λ_ M).hom ≫ ι
          := by
    rw [MonoidalClosed.uncurry_pre_app, toBidual, MonoidalClosed.uncurry_curry,
      BraidedCategory.braiding_naturality_left_assoc, MonoidalClosed.whiskerLeft_curry'_ihom_ev_app,
      ← Category.assoc, braiding_rightUnitor]
  have h2 : toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C) =
      ι ≫ (MonoidalClosed.unitIsoSelf (𝟙_ C)).inv := by
    rw [unitIsoSelf_inv, ← MonoidalClosed.curry_natural_left, leftUnitor_naturality, ← hk,
      MonoidalClosed.curry_uncurry]
  rw [← Category.assoc, h2, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end ZeroSchemeCanonMC

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace ZeroSchemeCanon

variable {X : Scheme.{u}}

private theorem comp_app_apply_of_eq {A B D : X.Modules} (f : A ⟶ B) (g : B ⟶ D)
    (h : A ⟶ D) (hfg : f ≫ g = h) (U : X.Opens) (x : Γ(A, U)) :
    g.app U (f.app U x) = h.app U x := by
  have happ : (f ≫ g).app U = h.app U := congrArg (fun k : A ⟶ D => k.app U) hfg
  have hValue := congrArg (fun k : Γ(A, U) ⟶ Γ(D, U) => k.hom x) happ
  exact hValue

theorem zeroSchemeIdeal_invModuleSection {I : X.IdealSheafData} (hI : I.IsInvertible) :
    zeroSchemeIdeal I.invModuleSection = I := by
  have hM : Scheme.Modules.IsInvertible I.invModule := hI.isInvertible_invModule
  have hj : IsIso (ZeroSchemeCanonMC.toBidual I.module) :=
    (hI.isInvertible_module.isIso_ev_app_and_isIso_curry_braiding_ev).2
  have hcomp : ZeroSchemeCanonMC.toBidual I.module ≫ sectionDual I.invModuleSection = I.moduleι :=
    ZeroSchemeCanonMC.toBidual_comp_pre_app_comp_unitIsoSelf_hom I.moduleι
  have hsd : sectionDual I.invModuleSection = inv (ZeroSchemeCanonMC.toBidual I.module) ≫
      I.moduleι := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
    rfl
  apply le_antisymm
  · refine zeroSchemeIdeal_le fun U => ?_
    rw [coeffIdeal, Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : Γ(Scheme.Modules.dual I.invModule, U.1),
        ihomSectionsEquiv I.invModule (𝟙_ X.Modules) U.1 t = φ ≫ (restrictUnitIso' U.1.ι).inv :=
      ⟨_, AddEquiv.apply_symm_apply _ _⟩
    have hφ : coeff I.invModuleSection U.1 φ =
        ofUnitSection U.1 ((sectionDual I.invModuleSection).app U.1 t) := by
      rw [ofUnitSection_sectionDual_app, ht, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hmem : (sectionDual I.invModuleSection).app U.1 t ∈ Set.range (I.moduleι.app U) :=
      ⟨(inv (ZeroSchemeCanonMC.toBidual I.module)).app U.1 t, by rw [hsd]; rfl⟩
    rw [(I.range_moduleIota_app_and_injective U).1] at hmem
    rw [hφ]
    exact hmem
  · rw [Scheme.IdealSheafData.le_def]
    intro U x hx
    have hx' : x ∈ Set.range (I.moduleι.app U) := by
      rw [(I.range_moduleIota_app_and_injective U).1]; exact hx
    obtain ⟨y, rfl⟩ := hx'
    let f : I.module ⟶ Scheme.Modules.dual I.invModule := ZeroSchemeCanonMC.toBidual I.module
    let t : Γ(Scheme.Modules.dual I.invModule, U.1) := f.app U.1 y
    have hfcomp : f ≫ sectionDual I.invModuleSection = I.moduleι := hcomp
    have hy : (sectionDual I.invModuleSection).app U.1 t = I.moduleι.app U.1 y :=
      comp_app_apply_of_eq f (sectionDual I.invModuleSection) I.moduleι hfcomp U.1 y
    change ofUnitSection U.1 (I.moduleι.app U.1 y) ∈ (zeroSchemeIdeal I.invModuleSection).ideal U
    rw [← hy, ofUnitSection_sectionDual_app]
    exact (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq _).1 U (coeff_mem_coeffIdeal _ U.1 _)

end ZeroSchemeCanon

end AlgebraicGeometry.Scheme.Modules

end

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    Scheme.Modules.zeroSchemeIdeal I.invModuleSection = I :=
  AlgebraicGeometry.Scheme.Modules.ZeroSchemeCanon.zeroSchemeIdeal_invModuleSection hI
end Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open
  _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

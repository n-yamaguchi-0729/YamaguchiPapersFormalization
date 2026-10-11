/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Adjunction.Mates
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev

/-!
# The inverse ideal module of a line-bundle section

An invertible module with an invertible zero-scheme ideal is isomorphic to the inverse ideal
module, carrying its section to the canonical section of that inverse module.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
open _root_.PresheafOfModules.PullbackMonoidal in
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

universe v u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

section MC
open _root_.CategoryTheory.MonoidalClosed
open _root_.CategoryTheory.BraidedCategory

namespace ZDIsoMC

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- The canonical map to the bidual, obtained by currying the braided evaluation map. -/
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
  rfl

omit [BraidedCategory C] in
theorem uncurry_eq_of_comp_unitIsoSelf_hom {X Y : C} (k : Y ⟶ (ihom (𝟙_ C)).obj X) (m : Y ⟶ X)
    (h : k ≫ (MonoidalClosed.unitIsoSelf X).hom = m) :
    MonoidalClosed.uncurry k = (λ_ Y).hom ≫ m := by
  have hk : k = m ≫ MonoidalClosed.curry (λ_ X).hom := by
    rw [← unitIsoSelf_inv, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hk, MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    leftUnitor_naturality]

theorem comp_toBidual_comp_pre_eq_curry' {M I : C} (s : 𝟙_ C ⟶ M) (ι : I ⟶ 𝟙_ C)
    (ψ : (ihom M).obj (𝟙_ C) ≅ I)
    (hψ : ψ.hom ≫ ι = (MonoidalClosed.pre s).app (𝟙_ C) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ C)).hom) :
    s ≫ toBidual M ≫ (MonoidalClosed.pre ψ.inv).app (𝟙_ C) = MonoidalClosed.curry' ι := by
  have hsev : s ▷ ((ihom M).obj (𝟙_ C)) ≫ (ihom.ev M).app (𝟙_ C) = (λ_ _).hom ≫ ψ.hom ≫ ι := by
    rw [show s ▷ ((ihom M).obj (𝟙_ C)) ≫ (ihom.ev M).app (𝟙_ C) =
      MonoidalClosed.uncurry ((MonoidalClosed.pre s).app (𝟙_ C)) from
        (MonoidalClosed.uncurry_pre s (𝟙_ C)).symm]
    exact uncurry_eq_of_comp_unitIsoSelf_hom _ _ hψ.symm
  symm
  rw [MonoidalClosed.curry', MonoidalClosed.curry_eq_iff, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre_app, toBidual, MonoidalClosed.uncurry_curry,
    whisker_exchange_assoc, braiding_naturality_right_assoc]
  calc (ρ_ I).hom ≫ ι = ψ.inv ▷ 𝟙_ C ≫ (ρ_ _).hom ≫ ψ.hom ≫ ι := by
        rw [rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]
    _ = ψ.inv ▷ 𝟙_ C ≫ (β_ _ _).hom ≫ (λ_ _).hom ≫ ψ.hom ≫ ι := by
        rw [← braiding_leftUnitor]; simp only [Category.assoc]
    _ = _ := by
        congr 2
        exact hsev.symm

end ZDIsoMC

end MC

open AlgebraicGeometry

namespace ZDIsoAssembly

variable {X : Scheme.{u}} {M : X.Modules}

theorem exists_iso_of_psi (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (I : X.IdealSheafData)
    (ψ : Scheme.Modules.dual M ≅ I.module) (hψ : ψ.hom ≫ I.moduleι = Scheme.Modules.sectionDual s) :
    ∃ e : M ≅ I.invModule, s ≫ e.hom = I.invModuleSection := by
  have h1 : IsIso (ZDIsoMC.toBidual M) := (hM.isIso_ev_app_and_isIso_curry_braiding_ev).2
  let e : M ⟶ I.invModule := ZDIsoMC.toBidual M ≫ (MonoidalClosed.pre ψ.inv).app (𝟙_ X.Modules)
  have h2 : IsIso ((MonoidalClosed.pre ψ.inv).app (𝟙_ X.Modules)) :=
    ⟨⟨(MonoidalClosed.pre ψ.hom).app (𝟙_ X.Modules), by
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.hom_inv_id,
        MonoidalClosed.pre_id]; rfl, by
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
        MonoidalClosed.pre_id]; rfl⟩⟩
  have : IsIso e := IsIso.comp_isIso' h1 h2
  refine ⟨asIso e, ?_⟩
  change s ≫ ZDIsoMC.toBidual M ≫ (MonoidalClosed.pre ψ.inv).app (𝟙_ X.Modules)
    = MonoidalClosed.curry' I.moduleι
  exact ZDIsoMC.comp_toBidual_comp_pre_eq_curry' s I.moduleι ψ hψ

end ZDIsoAssembly

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible) :
    ∃ e : M ≅ (Scheme.Modules.zeroSchemeIdeal s).invModule,
      s ≫ e.hom = (Scheme.Modules.zeroSchemeIdeal s).invModuleSection := by
  obtain ⟨ψ, hψ⟩ := hM.exists_dual_iso_module_zeroSchemeIdeal s hZ
  exact ZDIsoAssembly.exists_iso_of_psi hM s _ ψ hψ
end Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

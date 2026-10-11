/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal.lean
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
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module

/-!
# The dual module of a line-bundle section

The dual of an invertible module is identified with the module of its invertible zero-scheme
ideal, compatibly with the dual of the original section.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal
open _root_.PresheafOfModules.PullbackMonoidal in
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

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace SectionDualIso

variable {X : Scheme.{u}} {M : X.Modules}

/-- The section obtained by evaluating a morphism from the unit module at its unit section. -/
abbrev sVal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M, U) := s.app U (unitSection U)

lemma map_sVal (s : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op (sVal s U) = sVal s V := by
  have h := (NatTrans.naturality_apply s.mapPresheaf i.op (unitSection U)).symm
  rw [map_unitSection] at h
  exact h

lemma sectionDual_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (t : Γ(Scheme.Modules.dual M, U)) :
    (sectionDual s).app U t = ihomEval M (𝟙_ X.Modules) U (sVal s U) t := by
  change (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom.app U
      (((MonoidalClosed.pre s).app (𝟙_ X.Modules)).app U t) = _
  rw [unitIsoSelf_hom_app, ihomEval_pre_app]

lemma ofUnitSection_sectionDual_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    ofUnitSection U ((sectionDual s).app U t) =
      coeff s U (ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫ (restrictUnitIso' U.ι).hom) := by
  rw [sectionDual_app]
  have e1 := ihomSectionsEquiv_app_apply U t ⊤ (restrictSection s U)
  have e2 := restrictUnitIso_ι_hom_app_apply U ⊤
    ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  change _ = X.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((restrictUnitIso' U.ι).hom.app ⊤
        ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U)))
  rw [e2]
  change ihomEval M (𝟙_ X.Modules) U (sVal s U) t =
    (𝟙_ X.Modules).presheaf.map (eqToHom U.ι_image_top.symm).op
      ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  let m : Γ(M, U.ι ''ᵁ ⊤) := restrictSection s U
  let t' : Γ((ihom M).obj (𝟙_ X.Modules), U.ι ''ᵁ ⊤) :=
    ((Scheme.Modules.dual M).presheaf.map (homOfLE (U.ι_image_le ⊤)).op) t
  have e1' : (ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U) =
      ihomEval M (𝟙_ X.Modules) (U.ι ''ᵁ ⊤) m t' := e1
  rw [e1', map_ihomEval]
  congr 1
  · exact (map_sVal s _).symm
  · change t = ((Scheme.Modules.dual M).presheaf.map _ ≫ (Scheme.Modules.dual M).presheaf.map _) t
    rw [← Functor.map_comp, ← op_comp,
      show (eqToHom U.ι_image_top.symm ≫ homOfLE (U.ι_image_le ⊤) : U ⟶ U) = 𝟙 U from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
    rfl

lemma sectionDual_app_mem (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.affineOpens) (t : Γ(Scheme.Modules.dual M, V.1)) :
    ofUnitSection V.1 ((sectionDual s).app V.1 t) ∈ (zeroSchemeIdeal s).ideal V := by
  rw [ofUnitSection_sectionDual_app]
  exact (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).1 V (coeff_mem_coeffIdeal s V.1 _)

/-- The unit module on the zero subscheme, pushed forward to the ambient scheme. -/
def pushUnit (I : X.IdealSheafData) : X.Modules :=
  (show SheafOfModules X.ringCatSheaf from
    (SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf))

/-- Restriction of the ambient unit module to the unit module on the ideal subscheme. -/
def resMap (I : X.IdealSheafData) : 𝟙_ X.Modules ⟶ pushUnit I :=
  I.subschemeι.unitToPushforwardUnit

lemma resMap_app_moduleι_app (I : X.IdealSheafData) (U : X.Opens) (y : Γ(I.module, U)) :
    (resMap I).app U (I.moduleι.app U y) = 0 := by
  change ((kernel.ι I.subschemeι.unitToPushforwardUnit ≫ I.subschemeι.unitToPushforwardUnit).val.app
    (Opposite.op U)) y = 0
  rw [kernel.condition]
  rfl

lemma resMap_app_sectionDual_app (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (U : X.Opens) (t : Γ(Scheme.Modules.dual M, U)) :
    (resMap (zeroSchemeIdeal s)).app U ((sectionDual s).app U t) = 0 := by
  change (sectionDual s ≫ resMap (zeroSchemeIdeal s)).app U t = 0
  refine TopCat.Presheaf.IsSheaf.section_ext (pushUnit (zeroSchemeIdeal s)).isSheaf
    (U := Opposite.op U) ?_
  intro x hx
  obtain ⟨V, hxV, hVU, -⟩ := hM.exists_restrict_iso hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  rw [map_zero]
  have nat := (NatTrans.naturality_apply (sectionDual s ≫ resMap (zeroSchemeIdeal s)).mapPresheaf
    (homOfLE hVU).op t).symm
  refine nat.trans ?_
  change (resMap (zeroSchemeIdeal s)).app V.1 ((sectionDual s).app V.1
    ((Scheme.Modules.dual M).presheaf.map (homOfLE hVU).op t)) = 0
  obtain ⟨y, hy⟩ : (sectionDual s).app V.1
      ((Scheme.Modules.dual M).presheaf.map (homOfLE hVU).op t) ∈
        Set.range ((zeroSchemeIdeal s).moduleι.app V) := by
    rw [((zeroSchemeIdeal s).range_moduleIota_app_and_injective V).1]
    exact sectionDual_app_mem hM s V _
  rw [← hy]
  exact resMap_app_moduleι_app (zeroSchemeIdeal s) V.1 y

lemma sectionDual_comp_eq_zero (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    @CategoryStruct.comp (SheafOfModules.{u} X.ringCatSheaf) _
      (Scheme.Modules.dual M) (SheafOfModules.unit X.ringCatSheaf) _ (sectionDual s)
      (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit =
        (0 : Scheme.Modules.dual M ⟶ pushUnit (zeroSchemeIdeal s)) := by
  apply SheafOfModules.hom_ext
  ext U t
  change (resMap (zeroSchemeIdeal s)).app U.unop ((sectionDual s).app U.unop t) = 0
  exact resMap_app_sectionDual_app hM s U.unop t

lemma isIso_of_comp_moduleι_eq (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (I : X.IdealSheafData) (hI : zeroSchemeIdeal s = I) (hZ : I.IsInvertible)
    (ψ₀ : Scheme.Modules.dual M ⟶ I.module) (hψ₀ : ψ₀ ≫ I.moduleι = sectionDual s) :
    IsIso ψ₀ := by
  refine (IsInvertible.dual hM).1.isIso_of_locallySurjective hZ.isInvertible_module ψ₀ ?_
  intro U y x hx
  obtain ⟨V, hxV, hVU, ⟨τ⟩⟩ := hM.exists_restrict_iso hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  obtain ⟨hspan, -⟩ := (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 V τ
  rw [hI] at hspan
  have hmem : ofUnitSection V.1 (I.moduleι.app V.1 (I.module.presheaf.map (homOfLE hVU).op y)) ∈
      Ideal.span {coeff s V.1 τ.hom} := by
    rw [← hspan]
    have hr : I.moduleι.app V.1 (I.module.presheaf.map (homOfLE hVU).op y) ∈
        Set.range (I.moduleι.app V) := ⟨_, rfl⟩
    rw [(I.range_moduleIota_app_and_injective V).1] at hr
    exact hr
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Γ(Scheme.Modules.dual M, V.1),
      ihomSectionsEquiv M (𝟙_ X.Modules) V.1 t₀ = τ.hom ≫ (restrictUnitIso' V.1.ι).inv :=
    ⟨_, AddEquiv.apply_symm_apply _ _⟩
  refine ⟨a • t₀, ?_⟩
  apply (I.range_moduleIota_app_and_injective V).2
  apply ofUnitSection_injective V.1
  change ofUnitSection V.1 ((ψ₀ ≫ I.moduleι).app V.1 (a • t₀)) =
    ofUnitSection V.1 (I.moduleι.app V.1 (I.module.presheaf.map (homOfLE hVU).op y))
  rw [← ha, hψ₀, Scheme.Modules.Hom.app_smul, ofUnitSection_smul, ofUnitSection_sectionDual_app,
    ht₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem exists_dual_iso (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : (zeroSchemeIdeal s).IsInvertible) :
    ∃ ψ : Scheme.Modules.dual M ≅ (zeroSchemeIdeal s).module,
      ψ.hom ≫ (zeroSchemeIdeal s).moduleι = sectionDual s := by
  have h0 := sectionDual_comp_eq_zero hM s
  let ψ₀ : Scheme.Modules.dual M ⟶ (zeroSchemeIdeal s).module :=
    kernel.lift (C := SheafOfModules X.ringCatSheaf)
      (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit (sectionDual s) h0
  have hψ₀ : ψ₀ ≫ (zeroSchemeIdeal s).moduleι = sectionDual s :=
    kernel.lift_ι (C := SheafOfModules X.ringCatSheaf)
      (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit (sectionDual s) h0
  have : IsIso ψ₀ := isIso_of_comp_moduleι_eq hM s _ rfl hZ ψ₀ hψ₀
  exact ⟨asIso ψ₀, hψ₀⟩

end SectionDualIso

end AlgebraicGeometry.Scheme.Modules

end

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_dual_iso_module_zeroSchemeIdeal
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible) :
    ∃ ψ : Scheme.Modules.dual M ≅ (Scheme.Modules.zeroSchemeIdeal s).module,
      ψ.hom ≫ (Scheme.Modules.zeroSchemeIdeal s).moduleι = Scheme.Modules.sectionDual s :=
  AlgebraicGeometry.Scheme.Modules.SectionDualIso.exists_dual_iso hM s hZ
end Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

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

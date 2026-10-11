/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesProjectionMorphism
import SchemeTheory.Modules.PullbackLocalSection
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_epi_iff_locallySurjective
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_projectionMorphism_of_iso_free
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_pullback_map_projectionMorphism_iff
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_isIso_of_forall_exists_isIso_pullback_map
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Mathlib.Util.WithWeakNamespace

/-!
# Short exact sequences for powers of an invertible ideal

The unit map to the subscheme defined by an ideal power is an epimorphism, with
a short exact complex relating the indicated inverse ideal-module powers.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
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

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.Functor.LaxMonoidal
open _root_.CategoryTheory.Functor.OplaxMonoidal

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.uMod {X : Scheme.{u}} (I :
    X.IdealSheafData) :
    ((𝟙_ X.Modules : X.Modules) ⟶
      ((Scheme.Modules.pushforward I.subschemeι).obj (𝟙_ I.subscheme.Modules) : X.Modules)) :=
  I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.moduleι_comp_uMod {X : Scheme.{u}} (I
    : X.IdealSheafData) :
    I.moduleι ≫ I.uMod = 0 :=
  kernel.condition I.subschemeι.unitToPushforwardUnit

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.mono_moduleι' {X : Scheme.{u}} (I :
    X.IdealSheafData) :
    Mono I.moduleι :=
  ⟨fun _g _g' w => (cancel_mono (kernel.ι I.subschemeι.unitToPushforwardUnit)).mp w⟩

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.epi_uMod
    {X : Scheme.{u}} (I : X.IdealSheafData) : Epi I.uMod := by
  refine (AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective _).mpr ?_
  intro U s x hxU
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) hxU
  refine ⟨V, hVU, hxV, ?_⟩
  have hsurj := (isClosedImmersion_iff_isAffineHom.mp (inferInstance : IsClosedImmersion
      I.subschemeι)).2 V hV
  obtain ⟨a, ha⟩ := hsurj ((Scheme.Modules.presheaf ((SheafOfModules.pushforward
      I.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf))).map (homOfLE hVU).op s)
  exact ⟨a, ha⟩

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.unitSeq {X : Scheme.{u}} (I
    : X.IdealSheafData) :
    ShortComplex X.Modules :=
  ShortComplex.mk I.moduleι I.uMod I.moduleι_comp_uMod

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_unitSeq
    {X : Scheme.{u}} (I : X.IdealSheafData) : I.unitSeq.ShortExact := by
  have := I.epi_uMod
  have := I.mono_moduleι'
  refine ShortComplex.ShortExact.mk'
    ?_ (by change Mono I.moduleι; infer_instance)
    (by change Epi I.uMod; infer_instance)
  exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel I.subschemeι.unitToPushforwardUnit)

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.tensorSeq {X : Scheme.{u}}
    (I : X.IdealSheafData)
    (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (F ◁ I.moduleι) (F ◁ I.uMod)
    (by
      change (tensorLeft F).map _ ≫ (tensorLeft F).map _ = 0
      rw [← Functor.map_comp, I.moduleι_comp_uMod]
      exact Functor.map_zero _ _ _)

end AlgebraicGeometry.Scheme.IdealSheafData
namespace AlgebraicGeometry.Scheme.IdealSheafData
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.IdealSheafData in
private theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.shortExact_tensorSeq {X : Scheme.{u}}
    (I : X.IdealSheafData)
    {n : ℕ} (F : X.Modules) (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    (I.tensorSeq F).ShortExact := by
  have := I.mono_whiskerLeft_moduleIota F hF
  have := I.epi_uMod
  let G : X.Modules ⥤ X.Modules := tensorLeft F
  have hcok : IsColimit (CokernelCofork.ofπ (I.tensorSeq F).g (I.tensorSeq F).zero) := by
    have h0 := I.shortExact_unitSeq.gIsCokernel
    have h1 := CokernelCofork.mapIsColimit _ h0 G
    refine IsColimit.ofIsoColimit h1 (Cofork.ext (Iso.refl _) ?_)
    erw [Category.comp_id]
    rfl
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcok) ?_ ?_
  · change Mono (F ◁ I.moduleι); infer_instance
  · change Epi ((tensorLeft F).map I.uMod); infer_instance

end AlgebraicGeometry.Scheme.IdealSheafData
namespace Ws31IdealSES

variable {Z X : Scheme.{u}}

local instance invModulePowRightAdjoint (f : Z ⟶ X) :
    (SheafOfModules.pushforward.{u}
      (F := TopologicalSpace.Opens.map f.base)
      (J := _root_.Opens.grothendieckTopology X)
      (K := _root_.Opens.grothendieckTopology Z) f.toRingCatSheafHom).IsRightAdjoint :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint

theorem isIso_projectionMorphism (i : Z ⟶ X) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    IsIso (Scheme.Modules.projectionMorphism i G) := by
  apply Scheme.Modules.Hom.isIso_of_forall_exists_isIso_pullback_map
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hG.exists_trivialization x
  refine ⟨U, hx, ?_⟩
  rw [Scheme.Modules.isIso_pullback_map_projectionMorphism_iff]
  exact Scheme.Modules.isIso_projectionMorphism_of_iso_free (i ∣_ U) _ e

/-- The function corresponding to a section of the tensor-unit module. -/
abbrev toFun (U : X.Opens) (s : Γ(𝟙_ X.Modules, U)) : Γ(X, U) := s

lemma eq_smul_unitSection (U : X.Opens) (s : Γ(𝟙_ X.Modules, U)) :
    s = toFun U s • Scheme.Modules.unitSection U :=
  (Scheme.Modules.smul_unitSection (toFun U s)).symm

theorem pullbackTensorUnitObjIso_hom_app_pullbackLocalSection (f : Z ⟶ X) (U : X.Opens)
    (s : Γ(𝟙_ X.Modules, U)) :
    (Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection f s) =
      f.app U (toFun U s) := by
  conv_lhs => rw [eq_smul_unitSection U s]
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection]
  exact Scheme.Modules.smul_unitSection _

theorem η_pullback_eq (f : Z ⟶ X) :
    η (Scheme.Modules.pullback f) = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  apply Scheme.Modules.pullback_hom_ext
  intro U s
  change (Scheme.Modules.pullbackTensorUnitObjIso f).hom.app (f ⁻¹ᵁ U)
      (Scheme.Modules.pullbackLocalSection f s) = _
  rw [pullbackTensorUnitObjIso_hom_app_pullbackLocalSection]
  change _ = Scheme.Modules.Hom.app (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _
      _).symm
    f.unitToPushforwardUnit) (f ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection f s)
  erw [Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl

/-- The canonical map from the tensor-unit module to the pushed-forward tensor unit. -/
abbrev uX (i : Z ⟶ X) :
    ((𝟙_ X.Modules : X.Modules) ⟶ ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) : X.Modules))
        :=
  i.unitToPushforwardUnit

theorem unit_app_eq (i : Z ⟶ X) (G : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G =
      (λ_ G).inv ≫ (uX i ▷ G) ≫ Scheme.Modules.projectionMorphism i G := by
  rw [Scheme.Modules.projectionMorphism_def, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_id]
  congr 1
  rw [Scheme.Modules.projectionMorphismMate_def]
  rw [Functor.Monoidal.μIso_inv, ← δ_natural_left_assoc, ← comp_whiskerRight_assoc]
  have hc : (Scheme.Modules.pullback i).map (uX i) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) =
        η (Scheme.Modules.pullback i) := by
    rw [η_pullback_eq]
    rfl
  rw [hc, left_unitality_hom, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]

theorem rightUnitor_hom_comp_leftUnitor_inv (G : X.Modules) :
    (ρ_ G).hom ≫ (λ_ G).inv = (β_ G (𝟙_ X.Modules)).hom := by
  rw [← braiding_leftUnitor, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem whiskerLeft_moduleι_comp_unit (I : X.IdealSheafData) (G : X.Modules) :
    ((G ◁ I.moduleι) ≫ (ρ_ G).hom) ≫ (Scheme.Modules.pullbackPushforwardAdjunction
        I.subschemeι).unit.app G = 0 := by
  rw [unit_app_eq, Category.assoc, ← Category.assoc (ρ_ G).hom, rightUnitor_hom_comp_leftUnitor_inv,
    ← Category.assoc (β_ _ _).hom, ← BraidedCategory.braiding_naturality_right, Category.assoc, ←
        Category.assoc (G ◁ I.moduleι),
    ← MonoidalCategory.whiskerLeft_comp]
  change (tensorLeft G).map (I.moduleι ≫ I.uMod) ≫ _ = 0
  rw [I.moduleι_comp_uMod, Functor.map_zero, zero_comp]

theorem exists_shortExact_unit (I : X.IdealSheafData) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    ∃ w : ((G ◁ I.moduleι) ≫ (ρ_ G).hom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G = 0,
      (ShortComplex.mk ((G ◁ I.moduleι) ≫ (ρ_ G).hom)
        ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G) w).ShortExact := by
  have := isIso_projectionMorphism I.subschemeι G hG
  refine ⟨whiskerLeft_moduleι_comp_unit I G, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ (I.shortExact_tensorSeq G hG)
  refine ShortComplex.isoMk (Iso.refl _) (ρ_ G)
    ((β_ G _) ≪≫ asIso (Scheme.Modules.projectionMorphism I.subschemeι G)) ?_ ?_
  · change 𝟙 _ ≫ ((G ◁ I.moduleι) ≫ (ρ_ G).hom) = (G ◁ I.moduleι) ≫ (ρ_ G).hom
    rw [Category.id_comp]
  · change (ρ_ G).hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G =
      (G ◁ I.uMod) ≫ (β_ G _).hom ≫ Scheme.Modules.projectionMorphism I.subschemeι G
    rw [unit_app_eq, ← Category.assoc (ρ_ G).hom, rightUnitor_hom_comp_leftUnitor_inv,
      ← Category.assoc (β_ _ _).hom, ← BraidedCategory.braiding_naturality_right, Category.assoc]
    rfl

theorem epi_unit_app (I : X.IdealSheafData) {m : ℕ} (G : X.Modules)
    (hG : Scheme.Modules.IsLocallyFreeOfRank m G) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app G) := by
  obtain ⟨w, h⟩ := exists_shortExact_unit I G hG
  exact h.epi_g

end Ws31IdealSES

namespace Ws31EvKer

open Ws31IdealSES

variable {X : Scheme.{u}}


theorem nonempty_twistIso (𝓘 : X.IdealSheafData) (h𝓘 : 𝓘.IsInvertible) (L : X.Modules) (d n : ℕ) :
    Nonempty ((L ⊗ (𝓘 ^ (d + n)).invModule) ⊗ (𝓘 ^ n).module ≅ L ⊗ (𝓘 ^ d).invModule) := by
  obtain ⟨e431⟩ := (h𝓘.pow d).nonempty_mul_invModule_iso_tensor (h𝓘.pow n)
  obtain ⟨-, ⟨eMn⟩⟩ := (h𝓘.pow n).isInvertible_module.dual
  let ePow : (𝓘 ^ (d + n)).invModule ≅ (𝓘 ^ d * 𝓘 ^ n).invModule := eqToIso (by rw [pow_add])
  let eG : L ⊗ (𝓘 ^ (d + n)).invModule ≅ L ⊗ ((𝓘 ^ d).invModule ⊗ (𝓘 ^ n).invModule) :=
    whiskerLeftIso L (ePow ≪≫ e431)
  let eN : (𝓘 ^ n).invModule ⊗ (𝓘 ^ n).module ≅ 𝟙_ X.Modules := β_ _ _ ≪≫ eMn
  exact ⟨whiskerRightIso eG _ ≪≫ α_ L _ _ ≪≫
    whiskerLeftIso L (α_ _ _ _ ≪≫ whiskerLeftIso _ eN ≪≫ ρ_ _)⟩

theorem main (𝓘 : X.IdealSheafData) (h𝓘 : 𝓘.IsInvertible)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (r n d : ℕ) (hd : d + n = r) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app (L ⊗ (𝓘 ^
        r).invModule)) ∧
      ∃ (ι : L ⊗ (𝓘 ^ d).invModule ⟶ L ⊗ (𝓘 ^ r).invModule)
        (w : ι ≫ (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app
          (L ⊗ (𝓘 ^ r).invModule) = 0),
        (ShortComplex.mk ι _ w).ShortExact := by
  subst hd
  have hG : Scheme.Modules.IsInvertible (L ⊗ (𝓘 ^ (d + n)).invModule) :=
    hL.tensor (h𝓘.pow (d + n)).isInvertible_invModule
  have hG1 : Scheme.Modules.IsLocallyFreeOfRank 1 (L ⊗ (𝓘 ^ (d + n)).invModule) :=
    (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr hG
  obtain ⟨w, hS⟩ := exists_shortExact_unit (𝓘 ^ n) (L ⊗ (𝓘 ^ (d + n)).invModule) hG1
  obtain ⟨e⟩ := nonempty_twistIso 𝓘 h𝓘 L d n
  refine ⟨hS.epi_g, e.inv ≫ (((L ⊗ (𝓘 ^ (d + n)).invModule) ◁ (𝓘 ^ n).moduleι) ≫ (ρ_ _).hom), ?_,
      ?_⟩
  · rw [Category.assoc, w, comp_zero]
  · refine ShortComplex.shortExact_of_iso
      (S₁ := ShortComplex.mk ((((L ⊗ (𝓘 ^ (d + n)).invModule) ◁ (𝓘 ^ n).moduleι) ≫ (ρ_ _).hom))
        ((Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app
          (L ⊗ (𝓘 ^ (d + n)).invModule)) w) ?_ hS
    refine ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ ?_
    · change e.hom ≫ e.inv ≫ _ = _ ≫ 𝟙 _
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
    · change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]

end Ws31EvKer

end

with_weak_namespace _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
theorem epi_unit_app_tensor_invModule_pow_and_exists_shortExact
    {X : Scheme.{u}} (𝓘 : X.IdealSheafData) (h𝓘 : 𝓘.IsInvertible)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (r n d : ℕ) (hd : d + n = r) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app (L ⊗ (𝓘 ^
        r).invModule)) ∧
      ∃ (ι : L ⊗ (𝓘 ^ d).invModule ⟶ L ⊗ (𝓘 ^ r).invModule)
        (w : ι ≫ (Scheme.Modules.pullbackPushforwardAdjunction ((𝓘 ^ n).subschemeι)).unit.app
          (L ⊗ (𝓘 ^ r).invModule) = 0),
        (ShortComplex.mk ι _ w).ShortExact :=
  (open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
  open Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact in
      Ws31EvKer.main 𝓘 h𝓘 L hL r n d hd)
end Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
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
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
    AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
    AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
    AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
    AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
    AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
    AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
    AlgebraicGeometry.Scheme.Modules.map_unitSection
    AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
    AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
    AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
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

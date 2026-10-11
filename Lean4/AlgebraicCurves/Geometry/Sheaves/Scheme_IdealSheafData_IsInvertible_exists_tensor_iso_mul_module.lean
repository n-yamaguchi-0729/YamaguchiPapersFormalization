/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.RelativeDivisors.Cartier
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import SchemeTheory.Modules.TensorSectionMaps
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_leftUnitor_hom_app_tensorSections
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_range_moduleIota_app_and_injective
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Mathlib.Util.WithWeakNamespace

/-!
# Tensor products and products of invertible ideals

Multiplication of ideal sections induces a tensor map into the structure sheaf. This map
factors through the module of the product ideal; for invertible ideals the resulting map is
an isomorphism. The affine-local argument identifies its image with the product ideal.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb) in
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

noncomputable section

open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
namespace MulModule
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

lemma subschemeι_app_eq_zero_of_locally (K : X.IdealSheafData) {U : X.Opens} (r : Γ(X, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      K.subschemeι.app V (X.presheaf.map (homOfLE hVU).op r) = 0) :
    K.subschemeι.app U r = 0 := by
  let ι : Type u := {V : X.Opens // ∃ (hVU : V ≤ U),
    K.subschemeι.app V (X.presheaf.map (homOfLE hVU).op r) = 0}
  let W : ι → K.subscheme.Opens := fun V => K.subschemeι ⁻¹ᵁ V.1
  have hcover : K.subschemeι ⁻¹ᵁ U ≤ iSup W := by
    intro z hz
    obtain ⟨V, hVU, hzV, hV⟩ := h _ hz
    exact Opens.mem_iSup.2 ⟨⟨V, hVU, hV⟩, hzV⟩
  refine K.subscheme.sheaf.eq_of_locally_eq' W (K.subschemeι ⁻¹ᵁ U)
    (fun V => homOfLE (fun z hz => V.2.1 hz)) hcover _ _ (fun V => ?_)
  obtain ⟨hVU, hV⟩ := V.2
  have nat := ConcreteCategory.congr_hom (K.subschemeι.naturality (homOfLE hVU).op) r
  simp only [CommRingCat.comp_apply] at nat
  let q : Γ(K.subscheme, K.subschemeι ⁻¹ᵁ U) ⟶
      Γ(K.subscheme, K.subschemeι ⁻¹ᵁ V.1) :=
    K.subscheme.presheaf.map
      ((Opens.map K.subschemeι.base).map (homOfLE hVU)).op
  change q.hom (K.subschemeι.app U r) =
    q.hom (0 : Γ(K.subscheme, K.subschemeι ⁻¹ᵁ U))
  exact (nat.symm.trans hV).trans (map_zero q.hom).symm

/-- The structure-sheaf map obtained by restricting functions to the closed subscheme of `K`. -/
def toSubscheme (K : X.IdealSheafData) :
    ((𝟙_ X.Modules : X.Modules) ⟶
      ((Scheme.Modules.pushforward K.subschemeι).obj (𝟙_ K.subscheme.Modules) : X.Modules)) :=
  K.subschemeι.unitToPushforwardUnit

lemma toSubscheme_app (K : X.IdealSheafData) (U : X.Opens) (r : Γ(𝟙_ X.Modules, U)) :
    (toSubscheme K).app U r = K.subschemeι.app U (show Γ(X, U) from r) := rfl

variable (I J : X.IdealSheafData)

/-- Multiply the images of ideal sections in the structure sheaf. -/
def mulMap : I.module ⊗ J.module ⟶ 𝟙_ X.Modules :=
  (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom

lemma mulMap_app_tensorSections (U : X.Opens) (s : Γ(I.module, U)) (t : Γ(J.module, U)) :
    (show Γ(X, U) from (mulMap I J).app U (Scheme.Modules.tensorSections s t)) =
      (show Γ(X, U) from I.moduleι.app U s) * (show Γ(X, U) from J.moduleι.app U t) := by
  rw [mulMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.tensorHom_app_tensorSections]
  exact Scheme.Modules.leftUnitor_hom_app_tensorSections (N := 𝟙_ X.Modules)
    (show Γ(X, U) from I.moduleι.app U s) (J.moduleι.app U t)

lemma map_moduleι_app_mem_ideal (K : X.IdealSheafData) {U : X.Opens} (V : X.affineOpens)
    (hVU : (V : X.Opens) ≤ U) (s : Γ(K.module, U)) :
    X.presheaf.map (homOfLE hVU).op (show Γ(X, U) from K.moduleι.app U s) ∈ K.ideal V := by
  have h : (show Γ(X, V) from K.moduleι.app V (K.module.presheaf.map (homOfLE hVU).op s)) ∈
      (K.ideal V : Set Γ(X, V)) := by
    rw [← (K.range_moduleIota_app_and_injective V).1]
    exact ⟨_, rfl⟩
  rw [app_map] at h
  exact h

lemma mulMap_comp_toSubscheme : mulMap I J ≫ toSubscheme (I * J) = 0 := by
  apply Scheme.Modules.tensor_hom_ext
  intro U s t
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app, ConcreteCategory.comp_apply,
    toSubscheme_app]
  change (I * J).subschemeι.app U
    (show Γ(X, U) from (mulMap I J).app U (Scheme.Modules.tensorSections s t)) = 0
  rw [mulMap_app_tensorSections]
  apply subschemeι_app_eq_zero_of_locally
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hab : X.presheaf.map (homOfLE hVU).op
      ((show Γ(X, U) from I.moduleι.app U s) * (show Γ(X, U) from J.moduleι.app U t)) ∈
        (I * J).ideal ⟨V, hV⟩ := by
    rw [map_mul, ideal_mul]
    exact Ideal.mul_mem_mul (map_moduleι_app_mem_ideal I ⟨V, hV⟩ hVU s)
      (map_moduleι_app_mem_ideal J ⟨V, hV⟩ hVU t)
  rw [← (I * J).ker_subschemeι_app ⟨V, hV⟩, RingHom.mem_ker] at hab
  exact hab

/-- The multiplication map factored through the kernel defining the product-ideal module. -/
def mulLift : I.module ⊗ J.module ⟶ (I * J).module :=
  kernel.lift (C := SheafOfModules X.ringCatSheaf)
    (I * J).subschemeι.unitToPushforwardUnit (mulMap I J)
    (mulMap_comp_toSubscheme I J)
@[reassoc]
lemma mulLift_comp_moduleι : mulLift I J ≫ (I * J).moduleι = mulMap I J :=
  kernel.lift_ι (C := SheafOfModules X.ringCatSheaf) _ _ _

lemma moduleι_app_mulLift_app (U : X.Opens) (z : Γ(I.module ⊗ J.module, U)) :
    (I * J).moduleι.app U ((mulLift I J).app U z) = (mulMap I J).app U z := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, mulLift_comp_moduleι]

lemma mulLift_app_surjective (V : X.affineOpens) :
    Function.Surjective ((mulLift I J).app V) := by
  intro y
  obtain ⟨hrange, hinj⟩ := (I * J).range_moduleIota_app_and_injective V
  have hy : (show Γ(X, V) from (I * J).moduleι.app V y) ∈ I.ideal V * J.ideal V := by
    have : (show Γ(X, V) from (I * J).moduleι.app V y) ∈ ((I * J).ideal V : Set Γ(X, V)) := by
      rw [← hrange]; exact ⟨y, rfl⟩
    simp only [ideal_mul, Pi.mul_apply] at this
    exact this
  suffices H : ∀ r ∈ I.ideal V * J.ideal V,
      ∃ z, (show Γ(X, V) from (I * J).moduleι.app V ((mulLift I J).app V z)) = r by
    obtain ⟨z, hz⟩ := H _ hy
    exact ⟨z, hinj hz⟩
  intro r hr
  refine Submodule.mul_induction_on hr (fun a ha b hb => ?_) (fun c d hc hd => ?_)
  · have ha' : a ∈ Set.range (I.moduleι.app V) := by
      rw [(I.range_moduleIota_app_and_injective V).1]; exact ha
    have hb' : b ∈ Set.range (J.moduleι.app V) := by
      rw [(J.range_moduleIota_app_and_injective V).1]; exact hb
    obtain ⟨s, rfl⟩ := ha'
    obtain ⟨t, rfl⟩ := hb'
    exact ⟨Scheme.Modules.tensorSections s t, by
      rw [moduleι_app_mulLift_app]; exact mulMap_app_tensorSections I J V s t⟩
  · obtain ⟨z₁, rfl⟩ := hc
    obtain ⟨z₂, rfl⟩ := hd
    exact ⟨z₁ + z₂, by
      rw [map_add, map_add]
      rfl⟩

lemma mulLift_locallySurjective (U : X.Opens) (y : Γ((I * J).module, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (i : V ≤ U), x ∈ V ∧
      ((I * J).module).presheaf.map (homOfLE i).op y ∈ Set.range ((mulLift I J).app V) := by
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact ⟨V, hVU, hxV, mulLift_app_surjective I J ⟨V, hV⟩ _⟩

theorem isIso_mulLift {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    IsIso (mulLift I J) :=
  Scheme.Modules.IsInvertible.isIso_of_locallySurjective
    (hI.isInvertible_module.tensor hJ.isInvertible_module) (hI.mul hJ).isInvertible_module
    (mulLift I J) (mulLift_locallySurjective I J)

end AlgebraicGeometry.Scheme.IdealSheafData.MulModule

end

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
namespace MulModule
end AlgebraicGeometry.Scheme.IdealSheafData.MulModule
section
with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open scoped Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module.AlgebraicGeometry
namespace AlgebraicGeometry
open scoped Scheme
namespace Scheme
open scoped IdealSheafData
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace

theorem IdealSheafData.MulModule.exists_tensor_iso_mul_module
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    ∃ μ : I.module ⊗ J.module ≅ (I * J).module,
      μ.hom ≫ (I * J).moduleι = (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom := by
  have := IdealSheafData.MulModule.isIso_mulLift hI hJ
  exact ⟨asIso (IdealSheafData.MulModule.mulLift I J),
    IdealSheafData.MulModule.mulLift_comp_moduleι I J⟩

end Scheme
end AlgebraicGeometry
end

open _root_.AlgebraicGeometry in
open _root_.CategoryTheory.MonoidalCategory in
open _root_.Opposite in
open _root_.TopologicalSpace in
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.exists_tensor_iso_mul_module
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    ∃ μ : I.module ⊗ J.module ≅ (I * J).module,
      μ.hom ≫ (I * J).moduleι = (I.moduleι ⊗ₘ J.moduleι) ≫ (λ_ (𝟙_ X.Modules)).hom :=
  AlgebraicGeometry.Scheme.IdealSheafData.MulModule.exists_tensor_iso_mul_module hI hJ
end Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb) in
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

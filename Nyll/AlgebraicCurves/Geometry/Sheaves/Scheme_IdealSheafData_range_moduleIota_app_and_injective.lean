/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule

/-!
# The range of an ideal-module inclusion

On an affine open, the module inclusion is injective and its range is the
corresponding ideal of ring sections.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_range_moduleIota_app_and_injective

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Opposite in
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.range_moduleIota_app_and_injective {X :
  Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range (I.moduleι.app U) = (I.ideal U : Set Γ(X, U)) ∧
      Function.Injective (I.moduleι.app U) := by
  let R := X.ringCatSheaf
  let F := I.subschemeι.unitToPushforwardUnit
  let G : SheafOfModules R ⥤ ModuleCat (R.obj.obj (op (U : X.Opens))) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op (U : X.Opens))
  have : G.Additive := inferInstance
  have : PreservesLimit (parallelPair F 0) G := inferInstance
  let e₁ : G.obj (kernel F) ≅ kernel (G.map F) := PreservesKernel.iso G F
  let e₂ : kernel (G.map F) ≅ ModuleCat.of _ (LinearMap.ker (G.map F).hom) :=
    ModuleCat.kernelIsoKer (G.map F)
  have key : G.map (kernel.ι F) =
      e₁.hom ≫ e₂.hom ≫ ModuleCat.ofHom (LinearMap.ker (G.map F).hom).subtype := by
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom, kernelComparison_comp_ι]
  have hfun : ⇑(I.moduleι.app U) = Subtype.val ∘ ⇑(e₁ ≪≫ e₂).toLinearEquiv := by
    funext m
    change (G.map (kernel.ι F)).hom m = _
    rw [key]
    rfl
  have hbij : Function.Bijective ⇑(e₁ ≪≫ e₂).toLinearEquiv := (e₁ ≪≫ e₂).toLinearEquiv.bijective
  have hker : ∀ s, s ∈ LinearMap.ker (G.map F).hom ↔ s ∈ (I.ideal U : Set Γ(X, U)) := fun s ↦ by
    have h1 : s ∈ LinearMap.ker (G.map F).hom ↔ (I.subschemeι.app U).hom s = 0 :=
      LinearMap.mem_ker.trans Iff.rfl
    have h2 : s ∈ (I.ideal U : Set Γ(X, U)) ↔ (I.subschemeι.app U).hom s = 0 := by
      rw [← I.ker_subschemeι_app U]
      exact RingHom.mem_ker
    exact h1.trans h2.symm
  refine ⟨?_, ?_⟩
  · rw [hfun]
    ext s
    constructor
    · rintro ⟨m, rfl⟩
      exact (hker _).mp ((e₁ ≪≫ e₂).toLinearEquiv m).2
    · intro hs
      obtain ⟨m, hm⟩ := hbij.surjective ⟨s, (hker s).mpr hs⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  · rw [hfun]
    exact Subtype.val_injective.comp hbij.injective
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_IdealSheafData_range_moduleIota_app_and_injective
end ProofImplementation

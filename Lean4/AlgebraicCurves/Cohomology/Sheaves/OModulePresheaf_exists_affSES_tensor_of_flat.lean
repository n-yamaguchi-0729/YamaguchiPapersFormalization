/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafTensor
import SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# OModule Presheaf exists aff SES tensor of flat
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_exists_affSES_tensor_of_flat

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace P2mTensorExact

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (G : OModulePresheaf π)

/-- The sectionwise linear map induced by tensoring the given affine morphism with the identity. -/
noncomputable def appT {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) :
    (F.tensor G).obj U.1 →ₗ[R] (F'.tensor G).obj U.1 where
  toFun t := show (F'.tensor G).obj U.1 from
    (φ.appSections U).rTensor (G.obj U.1) (show F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1 from t)
  map_add' s t := map_add ((φ.appSections U).rTensor (G.obj U.1)) s t
  map_smul' r t := map_smul ((φ.appSections U).rTensor (G.obj U.1))
    ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t

theorem appT_apply {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens)
    (t : F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1) :
    appT G φ U (show (F.tensor G).obj U.1 from t) =
      (show (F'.tensor G).obj U.1 from (φ.appSections U).rTensor (G.obj U.1) t) := rfl

theorem appT_tmul {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) (x : F.obj U.1)
  (y : G.obj U.1) :
    appT G φ U (show (F.tensor G).obj U.1 from x ⊗ₜ y) = (show (F'.tensor G).obj U.1 from φ.app U x
      ⊗ₜ y) := rfl

/-- The affine morphism obtained by tensoring the given morphism on the right. -/
noncomputable def rTensorAffHom {F F' : OModulePresheaf π} (φ : AffHom F F') : AffHom (F.tensor G)
  (F'.tensor G) where
  app U := appT G φ U
  app_smul U a t := map_smul ((φ.appSections U).rTensor (G.obj U.1)) a t
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    change (φ.appSections U).rTensor (G.obj U.1) (F.tensorResₛₗ G h t) =
      F'.tensorResₛₗ G h ((φ.appSections U').rTensor (G.obj U'.1) t)
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [tensorResₛₗ_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, tensorResₛₗ_tmul,
        AffHom.appSections_apply, AffHom.appSections_apply, φ.naturality_apply h]
    | add s t hs ht => simp only [map_add, hs, ht]

theorem rTensorAffHom_app {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) :
    (rTensorAffHom G φ).app U = appT G φ U := rfl

variable {F₁ F₂ F₃ : OModulePresheaf π} (S : AffSES F₁ F₂ F₃)
  (hG : ∀ U : V.affineOpens, Module.Flat Γ(V, U.1) (G.obj U.1))

theorem exact_appSections (U : V.affineOpens) : Function.Exact (S.inc.appSections U)
  (S.proj.appSections U) := by
  have h : Function.Exact (S.inc.app U) (S.proj.app U) := LinearMap.exact_iff.mpr (S.exact U).symm
  exact h

/-- The affine short exact sequence obtained by tensoring with a module flat on affine opens. -/
noncomputable def affSES : AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G) where
  inc := rTensorAffHom G S.inc
  proj := rTensorAffHom G S.proj
  injective U := by
    have := hG U
    exact Module.Flat.rTensor_preserves_injective_linearMap (S.inc.appSections U) (S.injective U)
  surjective U := LinearMap.rTensor_surjective (G.obj U.1) (S.surjective U)
  exact U := by
    have := hG U
    have h := Module.Flat.rTensor_exact (G.obj U.1) (exact_appSections S U)
    have h' : Function.Exact ((rTensorAffHom G S.inc).app U) ((rTensorAffHom G S.proj).app U) := h
    exact (LinearMap.exact_iff.mp h').symm

include hG in
theorem main :
    ∃ S' : AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G),
      ∀ U : V.affineOpens,
        (∀ (x : F₁.obj U.1) (y : G.obj U.1),
          S'.inc.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₂.tensor G).obj U.1 from S.inc.app U x ⊗ₜ[Γ(V, U.1)] y)) ∧
        (∀ (x : F₂.obj U.1) (y : G.obj U.1),
          S'.proj.app U (show (F₂.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₃.tensor G).obj U.1 from S.proj.app U x ⊗ₜ[Γ(V, U.1)] y)) :=
  ⟨affSES G S hG, fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩

end P2mTensorExact

theorem _root_.AlgebraicGeometry.OModulePresheaf.exists_affSES_tensor_of_flat
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Module.Flat Γ(V, U.1) (G.obj U.1)) :
    ∃ S' : OModulePresheaf.AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G),
      ∀ U : V.affineOpens,
        (∀ (x : F₁.obj U.1) (y : G.obj U.1),
          S'.inc.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₂.tensor G).obj U.1 from S.inc.app U x ⊗ₜ[Γ(V, U.1)] y)) ∧
        (∀ (x : F₂.obj U.1) (y : G.obj U.1),
          S'.proj.app U (show (F₂.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₃.tensor G).obj U.1 from S.proj.app U x ⊗ₜ[Γ(V, U.1)] y)) :=
  P2mTensorExact.main G S hG
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_exists_affSES_tensor_of_flat
end ProofImplementation

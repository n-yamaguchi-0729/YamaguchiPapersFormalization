/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback

/-!
# Pullback of sections represented by module elements

The affine pullback comparison sends a module element represented as a section
to the section represented by its scalar extension.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.tilde_pullbackSpecIso_hom_app_top_unit_toOpen

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace tilde
open _root_.AlgebraicGeometry.tilde
end AlgebraicGeometry.tilde
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.tilde in
theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux {R S : CommRingCat.{u}} (φ : R ⟶ S) (M :
  ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj
          M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h2
  exact h2

theorem _root_.AlgebraicGeometry.tilde.pullbackSpecIso_hom_app_top_unit_toOpen {R S :
  CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by
  have h := congrArg (fun ψ => ψ.hom m) (AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux φ M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Adjunction.comp_unit_app] at h
  exact h

end AlgebraicCurves.Geometry.Sheaves.Proofs.tilde_pullbackSpecIso_hom_app_top_unit_toOpen
end ProofImplementation

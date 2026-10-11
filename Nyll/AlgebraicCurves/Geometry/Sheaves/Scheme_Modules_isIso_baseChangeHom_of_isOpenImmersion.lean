/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import Nyll.SchemeTheory.Modules.OpenImmersionUnit

/-!
# Base change along open immersions

The module base change comparison for a pullback square with an open immersion
is an isomorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_isOpenImmersion
    {X T Y S : Scheme.{u}} {π : X ⟶ T} {j : S ⟶ T} [IsOpenImmersion j] {ρ : Y ⟶ S} {u : Y ⟶ X}
    (hu : IsPullback u ρ π j) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom hu.w F) := by
  have : IsOpenImmersion u := by
    rw [show u = hu.isoPullback.hom ≫ pullback.fst π j from hu.isoPullback_hom_fst.symm]
    infer_instance
  have hrange : ∀ U : T.Opens, U ≤ j.opensRange → π ⁻¹ᵁ U ≤ u.opensRange := by
    intro U hU x hx
    obtain ⟨s, hs⟩ := hU hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := j) x s hs.symm
    refine ⟨hu.isoPullback.inv.base z, ?_⟩
    change (hu.isoPullback.inv ≫ u).base z = x
    rw [hu.isoPullback_inv_fst]
    exact hz
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  suffices h : ∀ W : S.Opens, W = j ⁻¹ᵁ (j ''ᵁ V) → IsIso ((Scheme.Modules.baseChangeHom hu.w F).app
      W) from
    h V (j.preimage_image_eq V).symm
  intro W hW
  subst hW
  have hUle : j ''ᵁ V ≤ j.opensRange := j.image_le_opensRange V
  have i1 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.Modules.bijective_unit_app_of_le_opensRange j _ _ hUle)
  have i2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app F).app (π ⁻¹ᵁ (j ''ᵁ
      V))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.Modules.bijective_unit_app_of_le_opensRange u F _ (hrange _ hUle))
  have key := Scheme.Modules.unit_app_app_comp_baseChangeHom_app π j ρ u hu.w F (j ''ᵁ V)
  have hc : IsIso ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) ≫
        (Scheme.Modules.baseChangeHom hu.w F).app (j ⁻¹ᵁ (j ''ᵁ V))) := by
    rw [key]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ i2 ?_
    first
      | exact Functor.map_isIso _ _
      | exact @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_op _)
  exact IsIso.of_isIso_comp_left (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
    ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) ((Scheme.Modules.baseChangeHom hu.w
        F).app (j ⁻¹ᵁ (j ''ᵁ V)))
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
end ProofImplementation

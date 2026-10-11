/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual

/-!
# Rigidifying an invertible module

Rigidification along a section preserves invertibility and identifies the original module
with the rigidified module tensored with the pullback of its value along the section.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_rigidify

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.rigidify
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (Scheme.Modules.rigidify σ q L) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj (Scheme.Modules.rigidify σ q L) ≅ 𝟙_ T.Modules)
          := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨hM, ⟨pairing⟩⟩ := Scheme.Modules.IsInvertible.dual hσL
  refine ⟨hL.tensor (Scheme.Modules.IsInvertible.pullback q hM), ⟨?_⟩⟩
  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)
  let e : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp σ q).app M ≪≫
      (Scheme.Modules.pullbackCongr hσq).app M ≪≫ (Scheme.Modules.pullbackId (X := T)).app M
  exact Scheme.Modules.pullbackTensorObjIso σ L _ ≪≫ (Iso.refl _ ⊗ᵢ e) ≪≫ pairing
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_rigidify
end ProofImplementation

open
  _root_.PresheafOfModules.PullbackMonoidal in
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
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

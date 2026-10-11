/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_pullback_dual

/-!
# Base change of rigidification

Rigidification of an invertible module commutes with pullback along a compatible square
of structure morphisms and sections.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    {T P T' P' : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} {σ' : T' ⟶ P'} {q' : P' ⟶ T'}
    (ψ : T' ⟶ T) (Ψ : P' ⟶ P) (hσ : σ' ≫ Ψ = ψ ≫ σ) (hq : Ψ ≫ q = q' ≫ ψ)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback Ψ).obj (Scheme.Modules.rigidify σ q L) ≅
      Scheme.Modules.rigidify σ' q' ((Scheme.Modules.pullback Ψ).obj L)) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨d⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ hσL
  let e₁ : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback σ).obj L) ≅
      (Scheme.Modules.pullback σ').obj ((Scheme.Modules.pullback Ψ).obj L) :=
    (Scheme.Modules.pullbackComp ψ σ).app L ≪≫ (Scheme.Modules.pullbackCongr hσ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp σ' Ψ).app L).symm
  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)
  let e₂ : (Scheme.Modules.pullback Ψ).obj ((Scheme.Modules.pullback q).obj M) ≅
      (Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback ψ).obj M) :=
    (Scheme.Modules.pullbackComp Ψ q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
      ((Scheme.Modules.pullbackComp q' ψ).app M).symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso Ψ L _ ≪≫
    (Iso.refl _ ⊗ᵢ (e₂ ≪≫ (Scheme.Modules.pullback q').mapIso
      (d ≪≫ Scheme.Modules.dualMapIso e₁)))⟩
end Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
end AlgebraicCurves.Geometry.Sheaves.Proofs
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

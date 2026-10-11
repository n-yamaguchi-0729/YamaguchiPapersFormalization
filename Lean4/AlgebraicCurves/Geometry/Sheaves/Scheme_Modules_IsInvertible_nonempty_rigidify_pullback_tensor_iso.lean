/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual_tensor

/-!
# Rigidification removes a tensor factor from the base

Rigidifying the tensor product of an invertible module with a module pulled back from
the base yields a module isomorphic to the rigidification of the original module.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

/-- The braided tensor interchange that exchanges the two middle factors of a fourfold tensor
    product. -/
def lbTB_tensorExchange {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V]
    (A B C D : V) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ (Iso.refl A ⊗ᵢ ((α_ B C D).symm ≪≫ (β_ B C ⊗ᵢ Iso.refl D) ≪≫ α_ C B D)) ≪≫
    (α_ A C (B ⊗ D)).symm

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q ((Scheme.Modules.pullback q).obj N ⊗ L) ≅
      Scheme.Modules.rigidify σ q L) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨_, ⟨pairN⟩⟩ := Scheme.Modules.IsInvertible.dual hN
  obtain ⟨dt⟩ := Scheme.Modules.IsInvertible.dual_tensor hN hσL
  let eN : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj N) ≅ N :=
    (Scheme.Modules.pullbackComp σ q).app N ≪≫ (Scheme.Modules.pullbackCongr hσq).app N ≪≫
      (Scheme.Modules.pullbackId (X := T)).app N
  let eD : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj
      ((Scheme.Modules.pullback q).obj N ⊗ L)) ≅
      Scheme.Modules.dual N ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ (eN ⊗ᵢ Iso.refl _)) ≪≫
      dt
  let eU : (Scheme.Modules.pullback q).obj N ⊗
      (Scheme.Modules.pullback q).obj (Scheme.Modules.dual N) ≅ 𝟙_ P.Modules :=
    (Scheme.Modules.pullbackTensorObjIso q N _).symm ≪≫ (Scheme.Modules.pullback q).mapIso pairN ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q
  refine ⟨?_⟩
  change ((Scheme.Modules.pullback q).obj N ⊗ L) ⊗ (Scheme.Modules.pullback q).obj _ ≅
    L ⊗ (Scheme.Modules.pullback q).obj _
  exact (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso eD ≪≫
      Scheme.Modules.pullbackTensorObjIso q _ _)) ≪≫
    lbTB_tensorExchange _ _ _ _ ≪≫ (eU ⊗ᵢ Iso.refl _) ≪≫ λ_ _
end Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
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

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.Cartier
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_pullback_dual
import AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule

/-!
# Pullback of inverse ideal modules

When an ideal sheaf and its inverse image are invertible, their inverse modules
are identified by pullback.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
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
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso
  {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj I.invModule ≅ (I.comap f).invModule) := by
  have hM₀ : Scheme.Modules.IsInvertible I.module := hI.isInvertible_module
  have hM : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback f).obj I.module) :=
    Scheme.Modules.IsInvertible.pullback f hM₀
  have hM' : Scheme.Modules.IsInvertible (I.comap f).module := hI'.isInvertible_module
  have : IsIso (I.pullbackModuleComparison f) :=
    Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hI hI'
  obtain ⟨e₁⟩ := Scheme.Modules.IsInvertible.pullback_dual f hM₀
  obtain ⟨e₂⟩ := CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    (asIso (I.pullbackModuleComparison f)) (Scheme.Modules.IsInvertible.dual hM).2
    (Scheme.Modules.IsInvertible.dual hM').2
  exact ⟨e₁ ≪≫ e₂⟩
end Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

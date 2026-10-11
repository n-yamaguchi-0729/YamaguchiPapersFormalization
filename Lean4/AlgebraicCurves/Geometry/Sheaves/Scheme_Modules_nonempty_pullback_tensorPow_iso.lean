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

import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.PullbackMonoidal

/-!
# Scheme Modules nonempty pullback tensor Pow iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_tensorPow_iso

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
  _root_.AlgebraicGeometry.Scheme.Modules in
/--
The isomorphism identifying the pullback of a tensor power with the tensor power of the
pullback.
-/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj
      L).tensorPow n
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso f
  | n + 1 => Scheme.Modules.pullbackTensorObjIso f (L.tensorPow n) L ≪≫
      whiskerRightIso (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f L n) _

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj (L.tensorPow n) ≅ ((Scheme.Modules.pullback f).obj
      L).tensorPow n) :=
  ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso f L n⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_tensorPow_iso
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
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

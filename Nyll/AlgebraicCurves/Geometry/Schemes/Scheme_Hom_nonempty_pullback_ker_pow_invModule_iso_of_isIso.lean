/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison

/-!
# Inverse ideal modules under isomorphic pullback

An isomorphism of schemes identifying two closed immersions transports powers of their
kernel ideals and the associated inverse ideal modules compatibly.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
open
  _root_.PresheafOfModules.PullbackMonoidal in
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
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace BCKerGlue
open _root_.AlgebraicGeometry


theorem comap_eq_map_inv {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (J : X.IdealSheafData) :
    J.comap f = J.map (inv f) := by
  apply le_antisymm
  · have h : ((J.map (inv f)).map f).comap f ≤ J.map (inv f) :=
      Scheme.IdealSheafData.comap_map_le (J.map (inv f)) f
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.map_id] at h
  · have h : J.map (inv f) ≤ ((J.comap f).map f).map (inv f) :=
      Scheme.IdealSheafData.map_mono (inv f) (Scheme.IdealSheafData.le_map_comap J f)
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.map_id] at h


theorem ker_comap_eq_ker {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) (p' : T ⟶ Y)
    (hp : p' ≫ f = p) : p.ker.comap f = p'.ker := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.map_ker, ← hp, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]


theorem comap_pow {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | succ n ih =>
      rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

end AlgebraicGeometry.BCKerGlue

open AlgebraicGeometry.BCKerGlue in
theorem _root_.AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) [IsClosedImmersion p] (p' : T ⟶ Y)
    (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).invModule) ≅ ((p'.ker) ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).module) ≅ ((p'.ker) ^ n).module) := by
  have hk : (p.ker ^ n).comap f = p'.ker ^ n := by
    rw [comap_pow, ker_comap_eq_ker f p p' hp]
  have hIn : (p.ker ^ n).IsInvertible := hI.pow n
  have hIn' : ((p.ker ^ n).comap f).IsInvertible := by
    rw [hk]
    exact hI'.pow n
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hIn hIn'
    exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hk)⟩
  · have h := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hIn hIn'
    exact ⟨@asIso _ _ _ _ ((p.ker ^ n).pullbackModuleComparison f) h ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hk)⟩
end Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

open
  _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
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
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

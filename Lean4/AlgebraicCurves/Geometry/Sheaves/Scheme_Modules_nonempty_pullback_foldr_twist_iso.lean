/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow

/-!
# Scheme Modules nonempty pullback foldr twist iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_foldr_twist_iso

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Scheme.Modules
  Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.pullback empty Modules IdealSheafData
  IdealSheafData.module IdealSheafData.invModule)

namespace IdealSheafData

export _root_.AlgebraicGeometry.Scheme.IdealSheafData (one_eq_top comap_top ideal comap module
  invModule pullbackModuleComparison IsInvertible isInvertible_top IsInvertible.mul comap_mul
  IsInvertible.isIso_pullbackModuleComparison IsInvertible.nonempty_pullback_invModule_iso
  IsInvertible.pow)


open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem comap_pow (I : Y.IdealSheafData) (n : ℕ) : (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_eq_top, comap_top]; rfl
  | succ k ih => rw [pow_succ, pow_succ, comap_mul, ih]

theorem comap_finset_prod {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_eq_top, comap_top]; rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, comap_mul, ih]

namespace IsInvertible
export _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible (mul
  isIso_pullbackModuleComparison nonempty_pullback_invModule_iso pow)
end IsInvertible

open scoped _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible in
theorem IsInvertible.finset_prod {ι : Type*} (s : Finset ι) (I : ι → Y.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact IsInvertible.mul (hI a (Finset.mem_insert_self a s)) (ih fun i hi => hI i
      (Finset.mem_insert_of_mem hi))

namespace IsInvertible

open scoped _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible in
private noncomputable def
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pullbackModuleIso {I :
  Y.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) : (Scheme.Modules.pullback f).obj I.module ≅ (I.comap
      f).module :=
  @asIso _ _ _ _ (I.pullbackModuleComparison f) (IsInvertible.isIso_pullbackModuleComparison f hI
    hI')

end IsInvertible

export _root_.AlgebraicGeometry.Scheme.IdealSheafData (IsInvertible.pullbackModuleIso)

namespace IsInvertible

open scoped _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible in
private noncomputable def
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.pullbackInvModuleIso {I :
  Y.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) : (Scheme.Modules.pullback f).obj I.invModule ≅ (I.comap
      f).invModule :=
  (IsInvertible.nonempty_pullback_invModule_iso f hI hI').some

end IsInvertible

export _root_.AlgebraicGeometry.Scheme.IdealSheafData (IsInvertible.pullbackInvModuleIso)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Scheme.Modules
  Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.pullback empty Modules IdealSheafData
  IdealSheafData.module IdealSheafData.invModule)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (pullback IsInvertible pullbackTensorObjIso)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry



open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData


variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem nonempty_pullback_prod_pow_twist_iso {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData)
    (aplus aminus : ι → ℕ) (hC : ∀ F, (C F).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible)
      :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module) ≅
      (∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module) := by
  have hprod : ∀ a : ι → ℕ, (∏ F, C F ^ a F).IsInvertible := fun a =>
    IsInvertible.finset_prod _ _ fun F _ => IsInvertible.pow (hC F) _
  have hcomap : ∀ a : ι → ℕ, (∏ F, C F ^ a F).comap f = ∏ F, (C F).comap f ^ a F := fun a => by
    rw [comap_finset_prod]
    exact Finset.prod_congr rfl fun F _ => comap_pow f (C F) (a F)
  have hprod' : ∀ a : ι → ℕ, ((∏ F, C F ^ a F).comap f).IsInvertible := fun a => by
    rw [hcomap]; exact IsInvertible.finset_prod _ _ fun F _ => IsInvertible.pow (hC' F) _
  exact ⟨pullbackTensorObjIso f _ _ ≪≫
    (((hprod aplus).pullbackInvModuleIso f (hprod' aplus) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.invModule (hcomap aplus))) ⊗ᵢ
      ((hprod aminus).pullbackModuleIso f (hprod' aminus) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.module (hcomap aminus))))⟩

theorem nonempty_pullback_foldr_twist_iso {m : ℕ} (K : Fin m → Y.IdealSheafData) (pos neg : Fin m →
  ℕ)
    {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData) (aplus aminus : ι → ℕ)
    (hK : ∀ j, (K j).IsInvertible) (hC : ∀ F, (C F).IsInvertible)
    (hK' : ∀ j, ((K j).comap f).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      (List.finRange m).foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg
        j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) := by
  suffices key : ∀ l : List (Fin m), Nonempty ((Scheme.Modules.pullback f).obj
        (l.foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      l.foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) from
          key _
  intro l
  induction l with
  | nil => exact nonempty_pullback_prod_pow_twist_iso f C aplus aminus hC hC'
  | cons j l ih =>
    obtain ⟨e⟩ := ih
    have hp : ∀ n : ℕ, (K j ^ n).IsInvertible := fun n => IsInvertible.pow (hK j) n
    have hp' : ∀ n : ℕ, ((K j ^ n).comap f).IsInvertible := fun n => by
      rw [comap_pow]; exact IsInvertible.pow (hK' j) n
    simp only [List.foldr_cons]
    exact ⟨pullbackTensorObjIso f _ _ ≪≫
      (((hp (pos j)).pullbackInvModuleIso f (hp' (pos j)) ≪≫
          eqToIso (congrArg Scheme.IdealSheafData.invModule (comap_pow f (K j) (pos j)))) ⊗ᵢ
        (pullbackTensorObjIso f _ _ ≪≫
          (((hp (neg j)).pullbackModuleIso f (hp' (neg j)) ≪≫
              eqToIso (congrArg Scheme.IdealSheafData.module (comap_pow f (K j) (neg j)))) ⊗ᵢ e)))⟩

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.Modules
  renaming nonempty_pullback_foldr_twist_iso → pullbackFoldrTwistProof in
theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_foldr_twist_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) {m : ℕ} (K : Fin m → Y.IdealSheafData) (pos neg : Fin m → ℕ)
    {ι : Type*} [Fintype ι] (C : ι → Y.IdealSheafData) (aplus aminus : ι → ℕ)
    (hK : ∀ j, (K j).IsInvertible) (hC : ∀ F, (C F).IsInvertible)
    (hK' : ∀ j, ((K j).comap f).IsInvertible) (hC' : ∀ F, ((C F).comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj
        ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
          ((∏ F, C F ^ aplus F).invModule ⊗ (∏ F, C F ^ aminus F).module)) ≅
      (List.finRange m).foldr (fun j N => ((K j).comap f ^ pos j).invModule ⊗ ((K j).comap f ^ neg
        j).module ⊗ N)
        ((∏ F, (C F).comap f ^ aplus F).invModule ⊗ (∏ F, (C F).comap f ^ aminus F).module)) :=
  pullbackFoldrTwistProof f K pos neg C aplus aminus hK hC hK' hC'
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_foldr_twist_iso
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
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
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

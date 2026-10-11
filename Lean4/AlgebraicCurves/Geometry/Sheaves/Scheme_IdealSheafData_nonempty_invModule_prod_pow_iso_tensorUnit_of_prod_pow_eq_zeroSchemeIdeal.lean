/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal

/-!
# Scheme Ideal Sheaf Data nonempty inv Module prod pow iso tensor Unit of prod pow eq zero
Scheme Ideal
-/

section ProofImplementation

namespace AlgebraicGeometry.Scheme.IdealSheafData
open _root_.SheafOfModules in
attribute [-instance]
  isIso_ihomModelToIhom
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
    {X : Scheme.{u}} {ι : Type u} [Fintype ι] (C : ι → X.IdealSheafData)
    (hC : ∀ i, (C i).IsInvertible) (mult : ι → ℕ)
    (t : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (hprod : ∏ i, C i ^ mult i = Scheme.Modules.zeroSchemeIdeal t) :
    Nonempty ((∏ i, C i ^ mult i).invModule ≅ 𝟙_ X.Modules) := by
  classical
  have hinv : ∀ s : Finset ι, (∏ i ∈ s, C i ^ mult i).IsInvertible := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
        exact Scheme.IdealSheafData.isInvertible_top
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact (Scheme.IdealSheafData.IsInvertible.pow (hC a) (mult a)).mul ih
  have hZ : (Scheme.Modules.zeroSchemeIdeal t).IsInvertible := by
    rw [← hprod]
    exact hinv Finset.univ
  obtain ⟨e, -⟩ := Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal (M := 𝟙_
    X.Modules)
    (Scheme.Modules.isInvertible_unit X) t hZ
  rw [hprod]
  exact ⟨e.symm⟩
end AlgebraicGeometry.Scheme.IdealSheafData
end ProofImplementation

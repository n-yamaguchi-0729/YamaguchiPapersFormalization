/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0

/-!
# One-dimensional sections of the unit sheaf on a fibre

A bijective scalar map identifies the global sections of the fibre with its field.
Transport along the identity-base-change isomorphism and the two-chart comparison
then computes the dimension of the zeroth cohomology of the unit sheaf.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FibreUnitSections

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard


theorem _root_.AlgebraicGeometry.RelPicard.finrank_H0_unit_fibreAt_eq_one_of_bijective_algebraMap
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    let _ : Algebra k Γ(pullback c x, ⊤) :=
      Scheme.TwoAffineOpenCover.algebraOfHom (pullback.snd c x) ⊤
    Function.Bijective (algebraMap k Γ(pullback c x, ⊤)) →
    ∀ (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit
          (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = 1 := by
  intro sourceAlgebra hH0 𝒲
  classical
  let Y : Scheme.{u} := pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x
  let y : Y ⟶ Spec (CommRingCat.of k) := fibreAt c (𝟙 _) x
  have hy : y = pullback.snd (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x := rfl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Y ≅ pullback c x, ψ.hom ≫ pullback.snd c x = y := by
    refine ⟨asIso (pullback.map (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x c x
      (pullback.fst c (𝟙 (Spec (CommRingCat.of R)))) (𝟙 _) (𝟙 _)
      (pullback.condition (f := c) (g := 𝟙 (Spec (CommRingCat.of R)))).symm
      (by rw [Category.comp_id, Category.id_comp])), ?_⟩
    rw [hy, asIso_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  let : Algebra k Γ(Y, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom y ⊤
  let : Module k Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), ⊤) :=
    Scheme.TwoAffineOpenCover.moduleSectionsOfHom y (SheafOfModules.unit Y.ringCatSheaf) ⊤
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒲 y
    (SheafOfModules.unit Y.ringCatSheaf)
  rw [← e.finrank_eq]
  have happ : ∀ {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of k)),
      f.appLE ⊤ ⊤ le_top = f.appTop := by
    intro Z f
    exact f.appLE_eq_app
  have hbij : Function.Bijective (algebraMap k Γ(Y, ⊤)) := by
    have hfac : (algebraMap k Γ(Y, ⊤) : k → Γ(Y, ⊤)) =
        (ψ.hom.appTop).hom ∘ (algebraMap k Γ(pullback c x, ⊤)) := by
      funext r
      change (y.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r) =
        (ψ.hom.appTop).hom (((pullback.snd c x).appLE ⊤ ⊤ le_top).hom
          ((Scheme.ΓSpecIso (.of k)).inv.hom r))
      rw [happ, happ, ← hψ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [hfac]
    exact (ConcreteCategory.bijective_of_isIso (ψ.hom.app ⊤)).comp hH0
  let f : k →ₗ[k] Γ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules), ⊤) :=
    { toFun := fun r => (algebraMap k Γ(Y, ⊤) r : Γ(Y, ⊤))
      map_add' := fun a b => by
        change algebraMap k Γ(Y, ⊤) (a + b) = algebraMap k Γ(Y, ⊤) a + algebraMap k Γ(Y, ⊤) b
        exact map_add _ a b
      map_smul' := fun a b => by
        change algebraMap k Γ(Y, ⊤) (a * b) = algebraMap k Γ(Y, ⊤) a * algebraMap k Γ(Y, ⊤) b
        exact map_mul _ a b }
  have hf : Function.Bijective f := hbij
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_self]
end JacobianVarieties.Picard.Proofs.FibreUnitSections
end ProofImplementation

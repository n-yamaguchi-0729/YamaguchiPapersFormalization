/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.LinearAlgebra.Dimension.Finrank
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0

/-!
# Scheme Two Affine Open Cover finrank H0 unit fibre eq one of bijective sections
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections

universe u

namespace H0UnitAux


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


variable {R : Type u} [CommRing R]

theorem finrank_H0_unit_eq_finrank_sections {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (x : X ⟶
  Spec (.of R)) :
    Module.finrank R (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf)).H0 =
      (letI := algebraOfHom x ⊤; Module.finrank R Γ(X, ⊤)) := by
  let := algebraOfHom x ⊤
  let := moduleSectionsOfHom x (SheafOfModules.unit X.ringCatSheaf) ⊤
  obtain ⟨e, -⟩ := exists_linearEquiv_sectionsOf_H0 𝒱 x (SheafOfModules.unit X.ringCatSheaf)
  let e0 : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) ≃ₗ[R] Γ(X, ⊤) :=
    { toFun := fun m => (m : Γ(X, ⊤))
      invFun := fun a => (a : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.finrank_eq, e0.finrank_eq]

theorem algebraMap_eq_appTop {Y : Scheme.{u}} (y : Y ⟶ Spec (.of R)) (r : R) :
    (algebraOfHom y ⊤).algebraMap r = y.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
  have happ : y.appLE ⊤ ⊤ le_top = y.appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [algebraMap_algebraOfHom, happ]

theorem appTop_algebraMap {X X' : Scheme.{u}} (x : X ⟶ Spec (.of R)) (x' : X' ⟶ Spec (.of R))
    (ψ : X ⟶ X') (hψ : ψ ≫ x' = x) (r : R) :
    ψ.appTop.hom ((algebraOfHom x' ⊤).algebraMap r) = (algebraOfHom x ⊤).algebraMap r := by
  rw [algebraMap_eq_appTop, algebraMap_eq_appTop, ← hψ, Scheme.Hom.comp_appTop]
  rfl

/-- The linear equivalence on global sections induced by an isomorphism of schemes over the base. -/
noncomputable def sectionsLinearEquiv {X X' : Scheme.{u}} (x : X ⟶ Spec (.of R)) (x' : X' ⟶ Spec
  (.of R))
    (ψ : X ≅ X') (hψ : ψ.hom ≫ x' = x) :
    letI := algebraOfHom x' ⊤; letI := algebraOfHom x ⊤
    Γ(X', ⊤) ≃ₗ[R] Γ(X, ⊤) :=
  letI := algebraOfHom x' ⊤; letI := algebraOfHom x ⊤
  { toFun := fun a => ψ.hom.appTop.hom a
    invFun := fun b => ψ.inv.appTop.hom b
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact appTop_algebraMap x x' ψ.hom hψ r
    left_inv := fun a => by
      change (ψ.hom.appTop ≫ ψ.inv.appTop).hom a = a
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    right_inv := fun b => by
      change (ψ.inv.appTop ≫ ψ.hom.appTop).hom b = b
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
      rfl }

theorem finrank_eq_one_of_bijective {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]
    (h : Function.Bijective (algebraMap k S)) : Module.finrank k S = 1 := by
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap k S) h).finrank_eq, Module.finrank_self]

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
        ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (k : Type u) [Field k]
    (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (Limits.pullback (Limits.pullback.snd c t)
      s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (Limits.pullback.snd (Limits.pullback.snd c t) s)
      (SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) s).ringCatSheaf)).H0 = 1 := by
  let : Algebra R k := (Spec.preimage (s ≫ t)).hom.toAlgebra
  have hspec : Scheme.TwoAffineOpenCover.specMap R k = s ≫ t := by
    change Spec.map (CommRingCat.ofHom (algebraMap R k)) = s ≫ t
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k)
  let x' : X' ⟶ Spec (.of k) := Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k)
  let ψ : Limits.pullback (Limits.pullback.snd c t) s ≅ X' :=
    pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hspec.symm
  have hψ : ψ.hom ≫ x' = Limits.pullback.snd (Limits.pullback.snd c t) s := by
    simp only [ψ, x', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map,
      pullback.lift_snd,
      Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_snd c t s
  rw [finrank_H0_unit_eq_finrank_sections 𝒲 (Limits.pullback.snd (Limits.pullback.snd c t) s)]
  let := algebraOfHom x' ⊤
  let := algebraOfHom (Limits.pullback.snd (Limits.pullback.snd c t) s) ⊤
  have e := sectionsLinearEquiv (Limits.pullback.snd (Limits.pullback.snd c t) s) x' ψ hψ
  rw [← e.finrank_eq]
  exact finrank_eq_one_of_bijective (hH0 k)

end H0UnitAux

end Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_TwoAffineOpenCover_finrank_H0_unit_fibre_eq_one_of_bijective_sections in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem finrank_H0_unit_fibre_eq_one_of_bijective_sections
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
        ⊤)))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (k : Type u) [Field k]
    (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (Limits.pullback (Limits.pullback.snd c t)
      s).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (Limits.pullback.snd (Limits.pullback.snd c t) s)
      (SheafOfModules.unit (Limits.pullback (Limits.pullback.snd c t) s).ringCatSheaf)).H0 = 1 :=
  H0UnitAux.main c hH0 t k s 𝒲
end AlgebraicGeometry.Scheme.TwoAffineOpenCover
end ProofImplementation

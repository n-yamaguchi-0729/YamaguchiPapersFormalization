/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.ModulesGlueOfCocycle
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul

/-!
# Scheme Modules exists iso glue Of Cocycle app eq glue Frame
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
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


open _root_.CategoryTheory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.map_smul
  Scheme.Modules.IsFrameOn Scheme.Modules.UnitCocycle Scheme.Modules.glueOfCocycle
  Scheme.Modules.glueFrame Scheme.Modules.isFrameOn_glueFrame Scheme.Modules.map_glueFrame_eq_smul
  Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Γ Modules Opens Modules.map_smul Modules.IsFrameOn
  Modules.UnitCocycle Modules.glueOfCocycle Modules.glueFrame Modules.isFrameOn_glueFrame
  Modules.map_glueFrame_eq_smul Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (presheaf map_smul IsFrameOn UnitCocycle
  glueOfCocycle glueFrame isFrameOn_glueFrame map_glueFrame_eq_smul
  exists_iso_app_eq_of_isFrameOn_of_eq_smul)

namespace GlueRecon

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry



open _root_.AlgebraicGeometry.Scheme.Modules.GlueOfCocycle


variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {A B : X.Opens} (h : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (r • m) = X.presheaf.map (homOfLE h).op r • M.presheaf.map
      (homOfLE h).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op m) = M.presheaf.map (homOfLE
      (hCB.trans hBA)).op m := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

theorem map_refl {A : X.Opens} (m : Γ(M, A)) : M.presheaf.map (homOfLE (le_refl A)).op m = m := by
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, M.presheaf.map_id]; rfl

theorem isFrameOn_unit_smul_map {A W : X.Opens} (hW : W ≤ A) {s : Γ(M, A)} (hs : IsFrameOn s A)
    (g : Γ(X, W)) (hg : IsUnit g) : IsFrameOn (g • M.presheaf.map (homOfLE hW).op s) W := by
  intro W' hW'W _
  have hg' : IsUnit (X.presheaf.map (homOfLE hW'W).op g) := hg.map _
  obtain ⟨v, hv⟩ := hg'
  have hb := hs (hW'W.trans hW) (hW'W.trans hW)
  have hcomp : (fun a : Γ(X, W') => a • M.presheaf.map (homOfLE hW'W).op (g • M.presheaf.map
    (homOfLE hW).op s)) =
      (fun a : Γ(X, W') => a • M.presheaf.map (homOfLE (hW'W.trans hW)).op s) ∘ (fun a => a * ↑v)
        := by
    funext a
    simp only [Function.comp_apply, map_smul', map_map, ← hv, smul_smul]
  rw [hcomp]
  exact hb.comp (Units.mulRight_bijective v)

end AlgebraicGeometry.Scheme.Modules.GlueRecon

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.GlueRecon AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c :
      Scheme.Modules.UnitCocycle U)
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) :
    ∃ φ : M ≅ Scheme.Modules.glueOfCocycle c, ∀ i, φ.hom.app (U i) (e i) = Scheme.Modules.glueFrame
      c i := by
  classical
  let G := Scheme.Modules.glueOfCocycle c
  let f : ∀ i, Γ(G, U i) := fun i => Scheme.Modules.glueFrame c i
  have hf : ∀ i, IsFrameOn (f i) (U i) := fun i => Scheme.Modules.isFrameOn_glueFrame c i
  have hftrans : ∀ i j, G.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (f j) =
      c.u i j • G.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (f i) :=
    fun i j => Scheme.Modules.map_glueFrame_eq_smul c i j
  let S : ∀ W : X.Opens, Set (Γ(M, W) × Γ(G, W)) := fun W =>
    {pq | ∃ (i : ι) (hW : W ≤ U i) (g : Γ(X, W)), IsUnit g ∧
      pq.1 = g • M.presheaf.map (homOfLE hW).op (e i) ∧ pq.2 = g • G.presheaf.map (homOfLE hW).op
        (f i)}
  have hframe : ∀ (W : X.Opens) (pq : Γ(M, W) × Γ(G, W)), pq ∈ S W → IsFrameOn pq.1 W ∧ IsFrameOn
    pq.2 W := by
    rintro W pq ⟨i, hW, g, hg, h1, h2⟩
    rw [h1, h2]
    exact ⟨isFrameOn_unit_smul_map hW (he i) g hg, isFrameOn_unit_smul_map hW (hf i) g hg⟩
  have hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty := by
    intro x
    have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨(M.presheaf.map (homOfLE (le_refl (U i))).op (e i), G.presheaf.map (homOfLE
      (le_refl (U i))).op (f i)),
      ⟨i, le_rfl, 1, isUnit_one, by rw [one_smul], by rw [one_smul]⟩⟩⟩
  have hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(M, W) × Γ(G, W)), pq ∈ S W →
      (M.presheaf.map (homOfLE h).op pq.1, G.presheaf.map (homOfLE h).op pq.2) ∈ S W' := by
    rintro W W' h pq ⟨i, hW, g, hg, h1, h2⟩
    refine ⟨i, h.trans hW, X.presheaf.map (homOfLE h).op g, hg.map _, ?_, ?_⟩
    · simp only [h1, map_smul', map_map]
    · simp only [h2, map_smul', map_map]
  have hunit : ∀ (W : X.Opens) (pq pq' : Γ(M, W) × Γ(G, W)), pq ∈ S W → pq' ∈ S W →
      ∃ w : Γ(X, W), pq'.1 = w • pq.1 ∧ pq'.2 = w • pq.2 := by
    rintro W pq pq' ⟨i, hW, g, hg, h1, h2⟩ ⟨j, hW', g', hg', h1', h2'⟩
    obtain ⟨v, hv⟩ := hg
    refine ⟨g' * rO (le_inf hW hW' : W ≤ U i ⊓ U j) (c.u i j) * ↑v⁻¹, ?_, ?_⟩
    · have ht := congrArg (M.presheaf.map (homOfLE (le_inf hW hW' : W ≤ U i ⊓ U j)).op) (htrans i j)
      rw [map_smul', map_map, map_map] at ht
      rw [h1', h1, ← hv, smul_smul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← smul_smul]
      erw [ht]
    · have ht := congrArg (G.presheaf.map (homOfLE (le_inf hW hW' : W ≤ U i ⊓ U j)).op) (hftrans i
        j)
      rw [map_smul', map_map, map_map] at ht
      rw [h2', h2, ← hv, smul_smul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← smul_smul]
      erw [ht]
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul S
    hframe hcov hres hunit
  refine ⟨φ, fun i => ?_⟩
  have hmem : (M.presheaf.map (homOfLE (le_refl (U i))).op (e i), G.presheaf.map (homOfLE (le_refl
    (U i))).op (f i)) ∈ S (U i) :=
    ⟨i, le_rfl, 1, isUnit_one, by rw [one_smul], by rw [one_smul]⟩
  have := hφ (U i) _ hmem
  rwa [map_refl, map_refl] at this
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
end ProofImplementation

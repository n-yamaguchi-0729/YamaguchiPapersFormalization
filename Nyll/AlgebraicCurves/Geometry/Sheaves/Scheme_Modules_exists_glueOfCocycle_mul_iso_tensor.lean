/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesGlueOfCocycle
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_tensorSections

/-!
# Scheme Modules exists glue Of Cocycle mul iso tensor
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor
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

export _root_.AlgebraicGeometry (Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme
  Scheme.Modules.Hom.id_app Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.tensorSections
  Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right
  Scheme.Modules.map_tensorSections Scheme.Modules.UnitCocycle Scheme.Modules.glueOfCocycle
  Scheme.Modules.glueFrame Scheme.Modules.isFrameOn_glueFrame Scheme.Modules.map_glueFrame_eq_smul
  Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom
  Modules.Hom.id_app Hom.comp_app Modules Opens Modules.map_smul Modules.tensorSections
  Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_tensorSections
  Modules.UnitCocycle Modules.glueOfCocycle Modules.glueFrame Modules.isFrameOn_glueFrame
  Modules.map_glueFrame_eq_smul Modules.exists_iso_glueOfCocycle_app_eq_glueFrame)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (presheaf Hom.comp_app Hom Hom.id_app map_smul
  tensorSections tensorSections_smul_left tensorSections_smul_right map_tensorSections IsFrameOn
  UnitCocycle glueOfCocycle glueFrame isFrameOn_glueFrame map_glueFrame_eq_smul
  exists_iso_glueOfCocycle_app_eq_glueFrame)

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

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme
  Scheme.Modules.Hom.id_app Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.tensorSections
  Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right
  Scheme.Modules.map_tensorSections Scheme.Modules.UnitCocycle Scheme.Modules.glueOfCocycle
  Scheme.Modules.glueFrame Scheme.Modules.isFrameOn_glueFrame Scheme.Modules.map_glueFrame_eq_smul
  Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Hom.id_app Hom Γ Modules.Hom.comp_app Modules.Hom
  Modules.Hom.id_app Hom.comp_app Modules Opens Modules.map_smul Modules.tensorSections
  Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_tensorSections
  Modules.UnitCocycle Modules.glueOfCocycle Modules.glueFrame Modules.isFrameOn_glueFrame
  Modules.map_glueFrame_eq_smul Modules.exists_iso_glueOfCocycle_app_eq_glueFrame)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (presheaf Hom.comp_app Hom Hom.id_app map_smul
  tensorSections tensorSections_smul_left tensorSections_smul_right map_tensorSections IsFrameOn
  UnitCocycle glueOfCocycle glueFrame isFrameOn_glueFrame map_glueFrame_eq_smul
  exists_iso_glueOfCocycle_app_eq_glueFrame)

namespace GlueRecon

open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem inv_app_hom_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    φ.inv.app U (φ.hom.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
    Scheme.Modules.Hom.id_app]
  rfl
end AlgebraicGeometry.Scheme.Modules.GlueRecon

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.GlueRecon AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_glueOfCocycle_mul_iso_tensor
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c c' :
      Scheme.Modules.UnitCocycle U) :
    ∃ φ : Scheme.Modules.glueOfCocycle (c.mul c') ≅ Scheme.Modules.glueOfCocycle c ⊗
      Scheme.Modules.glueOfCocycle c',
      ∀ i, φ.hom.app (U i) (Scheme.Modules.glueFrame (c.mul c') i) =
        Scheme.Modules.tensorSections (Scheme.Modules.glueFrame c i) (Scheme.Modules.glueFrame c'
          i) := by
  let e : ∀ i, Γ(Scheme.Modules.glueOfCocycle c ⊗ Scheme.Modules.glueOfCocycle c', U i) := fun i =>
    Scheme.Modules.tensorSections (Scheme.Modules.glueFrame c i) (Scheme.Modules.glueFrame c' i)
  have he : ∀ i, IsFrameOn (e i) (U i) := fun i =>
    (Scheme.Modules.isFrameOn_glueFrame c i).tensorSections (Scheme.Modules.isFrameOn_glueFrame c'
      i)
  have htrans : ∀ i j, (Scheme.Modules.glueOfCocycle c ⊗ Scheme.Modules.glueOfCocycle
    c').presheaf.map
        (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      (c.mul c').u i j • (Scheme.Modules.glueOfCocycle c ⊗ Scheme.Modules.glueOfCocycle
        c').presheaf.map
        (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i) := by
    intro i j
    simp only [e]
    rw [Scheme.Modules.map_tensorSections, Scheme.Modules.map_tensorSections,
      Scheme.Modules.map_glueFrame_eq_smul,
      Scheme.Modules.map_glueFrame_eq_smul, Scheme.Modules.tensorSections_smul_left,
        Scheme.Modules.tensorSections_smul_right,
      smul_smul]
    rfl
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hU
    (c.mul c') e he htrans
  refine ⟨φ.symm, fun i => ?_⟩
  rw [Iso.symm_hom, ← hφ i, inv_app_hom_app]
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor
end ProofImplementation

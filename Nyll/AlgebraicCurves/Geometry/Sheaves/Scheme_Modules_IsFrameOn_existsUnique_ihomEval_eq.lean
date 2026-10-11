/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections

/-!
# Scheme Modules Is Frame On exists Unique ihom Eval eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace N2P1

variable {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens}

theorem map_map (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M,
  V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem ihomSection_ext (p : Γ(P, V)) (hp : IsFrameOn p V) {θ θ' : Γ((ihom P).obj Q, V)}
    (h : ihomEval P Q V p θ = ihomEval P Q V p θ') : θ = θ' := by
  apply ihom_sections_ext
  intro W i m
  have hW : W ≤ V := i.le
  obtain ⟨g, rfl⟩ := (hp hW hW).2 m
  simp only
  have hi : i = homOfLE hW := Subsingleton.elim _ _
  subst hi
  rw [ihomEval_smul_left, ihomEval_smul_left, ← map_ihomEval, ← map_ihomEval, h]

/-- Coordinates of a section relative to the restriction of the chosen frame. -/
noncomputable def coeff (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) :
    Γ(P, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W) Γ(P, W) (P.presheaf.map (homOfLE
    hW).op p))
    (hp hW hW)).symm

theorem coeff_smul (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) (g : Γ(X, W)) :
    coeff p hp hW (g • P.presheaf.map (homOfLE hW).op p) = g := by
  apply (coeff p hp hW).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem smul_coeff (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) (x : Γ(P, W)) :
    coeff p hp hW x • P.presheaf.map (homOfLE hW).op p = x := by
  obtain ⟨g, rfl⟩ := (hp hW hW).2 x
  simp only
  rw [coeff_smul]

theorem exists_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃ θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q := by
  classical
  let fam : PresheafOfModules.InternalHom.PiFamily ((toPMod X).obj P) ((toPMod X).obj Q) (op V) :=
    fun Y f =>
      (show Γ(P, Y.unop) →ₗ[Γ(X, Y.unop)] Γ(Q, Y.unop) from
        (LinearMap.toSpanSingleton Γ(X, Y.unop) Γ(Q, Y.unop) (Q.presheaf.map (homOfLE
          f.unop.le).op q)).comp
          (coeff p hp f.unop.le).toLinearMap)
  have fam_apply : ∀ {Y : (X.Opens)ᵒᵖ} (f : op V ⟶ Y) (x : Γ(P, Y.unop)),
      fam f x = coeff p hp f.unop.le x • Q.presheaf.map (homOfLE f.unop.le).op q := fun f x => rfl
  have hfam : PresheafOfModules.InternalHom.IsNatural fam := by
    intro Y Z f g x
    change Q.presheaf.map g (fam f x) = fam (f ≫ g) (P.presheaf.map g x)
    erw [fam_apply f, fam_apply (f ≫ g)]
    have hg : g = (homOfLE g.unop.le).op := Subsingleton.elim _ _
    rw [hg, Q.map_smul, map_map]
    congr 1
    symm
    apply (coeff p hp (f ≫ (homOfLE g.unop.le).op).unop.le).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change _ = (X.presheaf.map (homOfLE g.unop.le).op (coeff p hp f.unop.le x)) •
      P.presheaf.map (homOfLE _).op p
    conv_lhs => rw [← smul_coeff p hp f.unop.le x]
    rw [P.map_smul, map_map]
  let φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj P) ((toPMod X).obj Q) (op
    V) :=
    ⟨fam, hfam⟩
  refine ⟨(SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property P Q (op
    V)).symm φ, ?_⟩
  change SheafOfModules.ihomEval X.sheaf.obj X.ringCatSheaf.property P Q (op V) p _ = q
  erw [SheafOfModules.ihomEval_def, AddEquiv.apply_symm_apply]
  change fam (𝟙 (op V)) p = q
  rw [fam_apply (𝟙 (op V))]
  change coeff p hp le_rfl p • Q.presheaf.map (homOfLE le_rfl).op q = q
  have h1 : coeff p hp (le_rfl : V ≤ V) p = 1 := by
    have := coeff_smul p hp (le_rfl : V ≤ V) 1
    rw [one_smul] at this
    have hp1 : P.presheaf.map (homOfLE (le_rfl : V ≤ V)).op p = p := by
      rw [Subsingleton.elim (homOfLE (le_rfl : V ≤ V)) (𝟙 V), op_id, P.presheaf.map_id]; rfl
    rw [hp1] at this
    exact this
  rw [h1, one_smul, Subsingleton.elim (homOfLE (le_rfl : V ≤ V)) (𝟙 V), op_id, Q.presheaf.map_id]
  rfl

theorem exists_unique_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q := by
  obtain ⟨θ, hθ⟩ := exists_ihomSection p hp q
  exact ⟨θ, hθ, fun θ' hθ' => ihomSection_ext p hp (hθ'.trans hθ.symm)⟩

end N2P1

open AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_ihomEval_eq {X :
  Scheme.{u}} {P Q : X.Modules} {V : X.Opens} {p : Γ(P, V)}
    (hp : Scheme.Modules.IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), Scheme.Modules.ihomEval P Q V p θ = q :=
  N2P1.exists_unique_ihomSection p hp q
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
end ProofImplementation

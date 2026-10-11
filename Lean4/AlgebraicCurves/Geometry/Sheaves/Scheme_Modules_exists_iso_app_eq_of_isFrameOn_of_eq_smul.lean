/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.Tactic.Choose
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

/-!
# Scheme Modules exists iso app eq of is Frame On of eq smul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.FrameIso

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace


open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme Scheme.Modules Scheme.Modules.IsFrameOn)

namespace FrameTorsorGlue

open _root_.AlgebraicGeometry


variable {X : Scheme.{u}} {P Q : X.Modules}

theorem map_le_refl {M : X.Modules} {W : X.Opens} (t : Γ(M, W)) :
    M.presheaf.map (homOfLE (le_refl W)).op t = t := by
  rw [Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, M.presheaf.map_id]; rfl

theorem isUnit_of_isFrameOn_smul {M : X.Modules} {W : X.Opens} {p : Γ(M, W)} {u : Γ(X, W)}
    (hp : IsFrameOn p W) (hp' : IsFrameOn (u • p) W) : IsUnit u := by
  obtain ⟨w, hw⟩ := (hp' (le_refl W) (le_refl W)).2 p
  simp only [map_le_refl] at hw
  have h1 : (w * u) • p = (1 : Γ(X, W)) • p := by rw [mul_smul, hw, one_smul]
  have hinj := (hp (le_refl W) (le_refl W)).1
  simp only [map_le_refl] at hinj
  have hwu : w * u = 1 := hinj h1
  exact IsUnit.of_mul_eq_one_right w hwu

/-- The internal-Hom section taking the specified local frame to the given section. -/
noncomputable def theta {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W)) :
    Γ((ihom P).obj Q, W) :=
  (IsFrameOn.existsUnique_ihomEval_eq (Q := Q) hp q).choose

theorem ihomEval_theta {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W)) :
    ihomEval P Q W p (theta p hp q) = q :=
  (IsFrameOn.existsUnique_ihomEval_eq (Q := Q) hp q).choose_spec.1

theorem eq_theta {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W))
    {θ : Γ((ihom P).obj Q, W)} (h : ihomEval P Q W p θ = q) : θ = theta p hp q :=
  (IsFrameOn.existsUnique_ihomEval_eq (Q := Q) hp q).unique h (ihomEval_theta p hp q)

theorem map_theta {W W' : X.Opens} (h : W' ≤ W) (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W))
    (hp' : IsFrameOn (P.presheaf.map (homOfLE h).op p) W') :
    ((ihom P).obj Q).presheaf.map (homOfLE h).op (theta p hp q) =
      theta (P.presheaf.map (homOfLE h).op p) hp' (Q.presheaf.map (homOfLE h).op q) := by
  apply eq_theta
  rw [← map_ihomEval, ihomEval_theta]

theorem theta_indep {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W))
    (u : Γ(X, W)) (hp' : IsFrameOn (u • p) W) :
    theta (u • p) hp' (u • q) = theta p hp q := by
  apply eq_theta
  have hu : IsUnit u := isUnit_of_isFrameOn_smul hp hp'
  have h2 := ihomEval_theta (Q := Q) (u • p) hp' (u • q)
  rw [ihomEval_smul_left] at h2
  exact hu.smul_left_cancel.mp h2

theorem main (S : ∀ W : X.Opens, Set (Γ(P, W) × Γ(Q, W)))
    (hframe : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      IsFrameOn pq.1 W ∧ IsFrameOn pq.2 W)
    (hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty)
    (hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      (P.presheaf.map (homOfLE h).op pq.1, Q.presheaf.map (homOfLE h).op pq.2) ∈ S W')
    (hunit : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)), pq ∈ S W → pq' ∈ S W →
      ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2) :
    ∃ e : P ≅ Q, ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → e.hom.app W pq.1 = pq.2 := by
  classical
  let Th : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → Γ((ihom P).obj Q, W) :=
    fun W pq h => theta pq.1 (hframe W pq h).1 pq.2
  have indep : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)) (h : pq ∈ S W) (h' : pq' ∈ S W),
      Th W pq h = Th W pq' h' := by
    intro W pq pq' h h'
    obtain ⟨u, h1, h2⟩ := hunit W pq pq' h h'
    obtain ⟨p', q'⟩ := pq'
    simp only at h1 h2
    subst h1
    subst h2
    exact (theta_indep pq.1 (hframe W pq h).1 pq.2 u (hframe W _ h').1).symm
  have res : ∀ (W W' : X.Opens) (hle : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)) (h : pq ∈ S W),
      ((ihom P).obj Q).presheaf.map (homOfLE hle).op (Th W pq h) = Th W' _ (hres W W' hle pq h) :=
    fun W W' hle pq h => map_theta hle pq.1 (hframe W pq h).1 pq.2 _
  have hdata : ∀ x : X, ∃ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), x ∈ W ∧ pq ∈ S W := by
    intro x
    obtain ⟨W, hx, pq, hpq⟩ := hcov x
    exact ⟨W, pq, hx, hpq⟩
  choose W pq hx hpq using hdata
  have hcovW : (⊤ : X.Opens) ≤ ⨆ x, W x := fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩
  let θ : ∀ x, Γ((ihom P).obj Q, W x) := fun x => Th (W x) (pq x) (hpq x)
  let FH : TopCat.Sheaf Ab X.carrier := ⟨((ihom P).obj Q).presheaf, ((ihom P).obj Q).isSheaf⟩
  have hcomp : TopCat.Presheaf.IsCompatible FH.1 W θ := by
    intro x z
    change ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op (θ x) =
      ((ihom P).obj Q).presheaf.map (homOfLE inf_le_right).op (θ z)
    simp only [θ]
    rw [res _ _ inf_le_left _ (hpq x), res _ _ inf_le_right _ (hpq z)]
    exact indep _ _ _ (hres _ _ inf_le_left _ (hpq x)) (hres _ _ inf_le_right _ (hpq z))
  obtain ⟨Θ, hΘ, -⟩ := FH.existsUnique_gluing' W ⊤ (fun x => homOfLE le_top) hcovW θ hcomp
  have hΘW : ∀ (V : X.Opens) (rs : Γ(P, V) × Γ(Q, V)) (h : rs ∈ S V),
      ((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ = Th V rs h := by
    intro V rs h
    apply FH.eq_of_locally_eq' (fun x => V ⊓ W x) V (fun x => homOfLE inf_le_left)
      (fun v hv => Opens.mem_iSup.mpr ⟨v, hv, hx v⟩)
    intro x
    change ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op
        (((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ) =
      ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op (Th V rs h)
    rw [res V (V ⊓ W x) inf_le_left rs h]
    have e1 : ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op
        (((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ) =
        ((ihom P).obj Q).presheaf.map (homOfLE (inf_le_right : V ⊓ W x ≤ W x)).op
          (((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ) := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply, ←
        Functor.map_comp]
      rfl
    rw [e1, hΘ x]
    change ((ihom P).obj Q).presheaf.map (homOfLE inf_le_right).op (Th (W x) (pq x) (hpq x)) = _
    rw [res (W x) (V ⊓ W x) inf_le_right (pq x) (hpq x)]
    exact indep _ _ _ (hres _ _ inf_le_right _ (hpq x)) (hres _ _ inf_le_left _ h)
  let μ : P ⟶ Q := ihomGlobalSectionsEquiv P Q Θ
  have hμ : ∀ (V : X.Opens) (rs : Γ(P, V) × Γ(Q, V)), rs ∈ S V → μ.app V rs.1 = rs.2 := by
    intro V rs h
    rw [ihomGlobalSectionsEquiv_app_apply, hΘW V rs h]
    exact ihomEval_theta _ _ _
  have : IsIso μ := isIso_of_isFrameOn_of_iSup_eq_top μ W (top_le_iff.mp hcovW)
    (fun x => (pq x).1) (fun x => (pq x).2)
    (fun x => (hframe _ _ (hpq x)).1) (fun x => (hframe _ _ (hpq x)).2) (fun x => hμ _ _ (hpq x))
  exact ⟨asIso μ, hμ⟩

end AlgebraicGeometry.FrameTorsorGlue

open _root_.AlgebraicGeometry
  _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.FrameIso.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul
    {X : Scheme.{u}} {P Q : X.Modules} (S : ∀ W : X.Opens, Set (Γ(P, W) × Γ(Q, W)))
    (hframe : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      Scheme.Modules.IsFrameOn pq.1 W ∧ Scheme.Modules.IsFrameOn pq.2 W)
    (hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty)
    (hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      (P.presheaf.map (homOfLE h).op pq.1, Q.presheaf.map (homOfLE h).op pq.2) ∈ S W')
    (hunit : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)), pq ∈ S W → pq' ∈ S W →
      ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2) :
    ∃ e : P ≅ Q, ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → e.hom.app W pq.1 = pq.2 := by
  exact FrameTorsorGlue.main S hframe hcov hres hunit
end AlgebraicCurves.Geometry.Sheaves.Proofs.FrameIso
end ProofImplementation

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

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum

/-!
# Proj Space exists twist Obj top forall res eq of mem H0 twist
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs6Glue

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]

/-- The degree-zero index for a single chart of the pulled-back standard cover. -/
def single (a : Fin (n + 1)) : (ProjSpace.stdCoverPullback ι).Idx 0 :=
  ⟨fun _ => ⟨a⟩, fun x y h => absurd h (by omega)⟩

theorem eq_single (s : (ProjSpace.stdCoverPullback ι).Idx 0) : s = single ι (s.1 0).down := by
  apply Subtype.ext
  funext k
  have hk : k = 0 := Fin.ext (by omega)
  subst hk
  rfl

theorem inter_single (a : Fin (n + 1)) :
    (ProjSpace.stdCoverPullback ι).inter (single ι a) = ProjSpace.pullbackChart ι a := by
  apply le_antisymm
  · exact Scheme.OrderedAffineCover.inter_le _ (single ι a) 0
  · refine le_iInf fun t => ?_
    change ProjSpace.pullbackChart ι a ≤ ProjSpace.pullbackChart ι a
    exact le_rfl

/-- The degree-one index for two strictly ordered charts of the pulled-back standard cover. -/
def pair (a b : Fin (n + 1)) (hab : a < b) : (ProjSpace.stdCoverPullback ι).Idx 1 :=
  ⟨fun j => if j = 0 then ⟨a⟩ else ⟨b⟩, by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    subst hi
    change (⟨a⟩ : ULift (Fin (n + 1))) < ⟨b⟩
    exact hab⟩

theorem face_pair_zero (a b : Fin (n + 1)) (hab : a < b) :
    (ProjSpace.stdCoverPullback ι).face (pair ι a b hab) 0 = single ι b := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.ext (by omega)
  subst hk; rfl

theorem face_pair_one (a b : Fin (n + 1)) (hab : a < b) :
    (ProjSpace.stdCoverPullback ι).face (pair ι a b hab) 1 = single ι a := by
  apply Subtype.ext; funext k
  have hk : k = 0 := Fin.ext (by omega)
  subst hk; rfl

theorem inter_single_inf_le_inter_pair (a b : Fin (n + 1)) (hab : a < b) :
    (ProjSpace.stdCoverPullback ι).inter (single ι a) ⊓ (ProjSpace.stdCoverPullback ι).inter
      (single ι b)
      ≤ (ProjSpace.stdCoverPullback ι).inter (pair ι a b hab) := by
  refine le_iInf fun t => ?_
  change _ ≤ (ProjSpace.stdCoverPullback ι).U (if t = 0 then ⟨a⟩ else ⟨b⟩)
  by_cases ht : t = 0
  · erw [ite_eq_left ht]
    exact inf_le_left.trans (Scheme.OrderedAffineCover.inter_le _ (single ι a) 0)
  · erw [ite_eq_right ht]
    exact inf_le_right.trans (Scheme.OrderedAffineCover.inter_le _ (single ι b) 0)

end P2mWs6Glue

open P2mWs6Glue in
theorem _root_.AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (φ : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom φ] (m : ℕ)
    (c : (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).cochain (ProjSpace.stdCoverPullback φ) 0)
    (hc : c ∈ (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).H0 (ProjSpace.stdCoverPullback φ)) :
    ∃ g : ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m ⊤,
      ∀ s : (ProjSpace.stdCoverPullback φ).Idx 0,
        (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).res (le_top : (ProjSpace.stdCoverPullback
          φ).inter s ≤ ⊤) g = c s := by
  classical
  have hC : ∀ (i : Fin (n + 1)) (s₁ s₂ : (ProjSpace.stdCoverPullback φ).Idx 0), s₁ = s₂ → ∀ (W :
    Z.Opens)
      (h₁ : W ≤ (ProjSpace.stdCoverPullback φ).inter s₁ ⊓ ProjSpace.pullbackChart φ i) (h₂ : W ≤
        (ProjSpace.stdCoverPullback φ).inter s₂ ⊓ ProjSpace.pullbackChart φ i),
      ProjSpace.restrictFun h₁ ((c s₁).val i) = ProjSpace.restrictFun h₂ ((c s₂).val i) := by
    rintro i s₁ s₂ rfl W h₁ h₂; rfl
  have hcyc : ∀ (t : (ProjSpace.stdCoverPullback φ).Idx 1) (i : Fin (n + 1)) (W : Z.Opens) (hW : W
    ≤ (ProjSpace.stdCoverPullback φ).inter t ⊓ ProjSpace.pullbackChart φ i),
      ProjSpace.restrictFun (hW.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback
        φ).inter_le_inter_face t 0))) ((c ((ProjSpace.stdCoverPullback φ).face t 0)).val i)
        = ProjSpace.restrictFun (hW.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback
          φ).inter_le_inter_face t 1))) ((c ((ProjSpace.stdCoverPullback φ).face t 1)).val i) := by
    intro t i W hW
    have h0 : (ProjSpace.twist (φ ≫ ProjSpace.π A n) φ m).d (ProjSpace.stdCoverPullback φ) 0 c t =
      0 := by
      rw [LinearMap.mem_ker.mp hc]; rfl
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, add_neg_eq_zero]
      at h0
    have h1 := congrArg (fun g : ProjSpace.twistObj (φ ≫ ProjSpace.π A n) φ m
      ((ProjSpace.stdCoverPullback φ).inter t) => g.val i) h0
    change ProjSpace.restrictFun
        (inf_le_inf_right (ProjSpace.pullbackChart φ i) ((ProjSpace.stdCoverPullback
          φ).inter_le_inter_face t 0))
        ((c ((ProjSpace.stdCoverPullback φ).face t 0)).val i) =
      ProjSpace.restrictFun
        (inf_le_inf_right (ProjSpace.pullbackChart φ i) ((ProjSpace.stdCoverPullback
          φ).inter_le_inter_face t 1))
        ((c ((ProjSpace.stdCoverPullback φ).face t 1)).val i) at h1
    have h2 := congrArg (ProjSpace.restrictFun hW) h1
    rw [ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun] at h2
    exact h2
  have hcov : ∀ (V : Z.Opens) (i : Fin (n + 1)), V ⊓ ProjSpace.pullbackChart φ i ≤ ⨆ s :
    (ProjSpace.stdCoverPullback φ).Idx 0, ((ProjSpace.stdCoverPullback φ).inter s ⊓
    ProjSpace.pullbackChart φ i) := by
    intro V i x hx
    have hx' : x ∈ (⊤ : Z.Opens) := trivial
    rw [← (ProjSpace.stdCoverPullback φ).iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at hx'
    obtain ⟨a, ha⟩ := hx'
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨single φ a.down, ?_⟩
    refine ⟨?_, hx.2⟩
    rw [inter_single]
    exact ha
  have hcompat : ∀ (i : Fin (n + 1)) (s s' : (ProjSpace.stdCoverPullback φ).Idx 0) (W : Z.Opens)
      (h : W ≤ (ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) (h' : W ≤
        (ProjSpace.stdCoverPullback φ).inter s' ⊓ ProjSpace.pullbackChart φ i),
      ProjSpace.restrictFun h ((c s).val i) = ProjSpace.restrictFun h' ((c s').val i) := by
    intro i s s' W h h'
    have hs := eq_single φ s
    have hs' := eq_single φ s'
    rcases lt_trichotomy (s.1 0).down (s'.1 0).down with hlt | heq | hgt
    · let t := pair φ _ _ hlt
      have hWt : W ≤ (ProjSpace.stdCoverPullback φ).inter t ⊓ ProjSpace.pullbackChart φ i := by
        refine le_inf ?_ (h.trans inf_le_right)
        refine (le_inf (h.trans inf_le_left) (h'.trans inf_le_left)).trans ?_
        rw [hs, hs']
        exact inter_single_inf_le_inter_pair φ _ _ hlt
      have e0 : (ProjSpace.stdCoverPullback φ).face t 0 = s' := (face_pair_zero φ _ _ hlt).trans
        hs'.symm
      have e1 : (ProjSpace.stdCoverPullback φ).face t 1 = s := (face_pair_one φ _ _ hlt).trans
        hs.symm
      rw [hC i s _ e1.symm W h (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback
        φ).inter_le_inter_face t 1))),
        hC i s' _ e0.symm W h' (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback
          φ).inter_le_inter_face t 0)))]
      exact (hcyc t i W hWt).symm
    · have : s = s' := by rw [hs, hs', heq]
      exact hC i s s' this W h h'
    · let t := pair φ _ _ hgt
      have hWt : W ≤ (ProjSpace.stdCoverPullback φ).inter t ⊓ ProjSpace.pullbackChart φ i := by
        refine le_inf ?_ (h.trans inf_le_right)
        refine (le_inf (h'.trans inf_le_left) (h.trans inf_le_left)).trans ?_
        rw [hs, hs']
        exact inter_single_inf_le_inter_pair φ _ _ hgt
      have e0 : (ProjSpace.stdCoverPullback φ).face t 0 = s := (face_pair_zero φ _ _ hgt).trans
        hs.symm
      have e1 : (ProjSpace.stdCoverPullback φ).face t 1 = s' := (face_pair_one φ _ _ hgt).trans
        hs'.symm
      rw [hC i s _ e0.symm W h (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback
        φ).inter_le_inter_face t 0))),
        hC i s' _ e1.symm W h' (hWt.trans (inf_le_inf_right _ ((ProjSpace.stdCoverPullback
          φ).inter_le_inter_face t 1)))]
      exact hcyc t i W hWt
  have hglue : ∀ i : Fin (n + 1), ∃ gi : Γ(Z, (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i),
      ∀ s : (ProjSpace.stdCoverPullback φ).Idx 0, ProjSpace.restrictFun (inf_le_inf_right
        (ProjSpace.pullbackChart φ i) le_top :
        (ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i ≤ (⊤ : Z.Opens) ⊓
          ProjSpace.pullbackChart φ i) gi = (c s).val i := by
    intro i
    have := Z.sheaf.existsUnique_gluing' (fun s : (ProjSpace.stdCoverPullback φ).Idx 0 =>
      (ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i)
      ((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) (fun s => homOfLE (inf_le_inf_right
        (ProjSpace.pullbackChart φ i) le_top)) (hcov ⊤ i)
      (fun s => (c s).val i) (fun s s' => hcompat i s s' _ inf_le_left inf_le_right)
    obtain ⟨gi, hgi, -⟩ := this
    exact ⟨gi, hgi⟩
  choose gf hgf using hglue
  have hTC : ProjSpace.TwistCompat φ m ⊤ gf := by
    intro i j
    apply Z.sheaf.eq_of_locally_eq' (fun s : (ProjSpace.stdCoverPullback φ).Idx 0 =>
      ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) ⊓
      ProjSpace.pullbackChart φ j)
      (((⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) ⊓ ProjSpace.pullbackChart φ j)
      (fun s => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ le_top)))
    · intro x hx
      have := hcov ⊤ i ⟨hx.1.1, hx.1.2⟩
      rw [TopologicalSpace.Opens.mem_iSup] at this ⊢
      obtain ⟨s, hs⟩ := this
      exact ⟨s, hs, hx.2⟩
    · intro s
      change ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (gf i)) =
        ProjSpace.restrictFun _ (ProjSpace.restrictFun _ (ProjSpace.frameUnit φ i j) ^ m *
          ProjSpace.restrictFun _ (gf j))
      rw [map_mul, map_pow, ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun,
        ProjSpace.restrictFun_restrictFun]
      have hi : ProjSpace.restrictFun ((inf_le_left.trans (inf_le_inf_right
        (ProjSpace.pullbackChart φ i) le_top)) :
          ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) ⊓
            ProjSpace.pullbackChart φ j ≤ (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ i) (gf i)
          = ProjSpace.restrictFun inf_le_left ((c s).val i) := by
        rw [← hgf i s, ProjSpace.restrictFun_restrictFun]
      have hj : ProjSpace.restrictFun ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans
            (inf_le_inf_right (ProjSpace.pullbackChart φ j) le_top) :
          ((ProjSpace.stdCoverPullback φ).inter s ⊓ ProjSpace.pullbackChart φ i) ⊓
            ProjSpace.pullbackChart φ j ≤ (⊤ : Z.Opens) ⊓ ProjSpace.pullbackChart φ j) (gf j)
          = ProjSpace.restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ((c s).val
            j) := by
        rw [← hgf j s, ProjSpace.restrictFun_restrictFun]
      rw [hi, hj]
      exact (c s).compat i j
  refine ⟨⟨gf, hTC⟩, fun s => ?_⟩
  apply ProjSpace.twistObj.ext
  funext i
  rw [ProjSpace.twist_res_val]
  exact hgf i s
end ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation

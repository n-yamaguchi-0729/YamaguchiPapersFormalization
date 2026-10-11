/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Opposites
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set
import Mathlib.Topology.Category.TopCat.Opens
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverOf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayDoubleComplex
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_aug_injective

/-!
# OModule Presheaf exists box zigzag of d eq zero of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace G1SlabZigzagAux

variable {P : Scheme.{u}}

/-- Restriction of regular sections to a smaller open. -/
noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

section Main

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover) (U : X.Opens)

omit [IsSeparated fX] in
theorem isSeparated_fst (hP : IsPullback p₁ p₂ fX fY) : IsSeparated p₁ :=
  MorphismProperty.of_isPullback hP.flip (inferInstance : IsSeparated fY)

omit [IsSeparated fX] in
theorem isAffineOpen_strip (hP : IsPullback p₁ p₂ fX fY) (hU : IsAffineOpen U) {a : ℕ} (σ : 𝒱.Idx
  a) :
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) := by
  have hV : IsAffineOpen (𝒱.inter σ) := Scheme.OrderedAffineCover.isAffineOpen_inter fY 𝒱 σ
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of k))
  have hsq := Scheme.Hom.isPullback_resLE hP (US := ⊤) (UT := 𝒱.inter σ) (UX := U)
    (by simp) (by simp) (UY := p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) rfl
  exact .of_isIso hsq.isoPullback.hom

theorem restrict_inter {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R)) [IsSeparated π]
    {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  change (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end Main

end G1SlabZigzagAux

end OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
end AlgebraicCurves.Cohomology.Sheaves.Proofs

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

open AlgebraicCurves.Cohomology.Sheaves.Proofs in
open OModulePresheaf_exists_box_zigzag_of_d_eq_zero_of_isAffineOpen.G1SlabZigzagAux in
theorem exists_box_zigzag_of_d_eq_zero_of_isAffineOpen
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
      (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)),
      (∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
        (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
                (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t
                  j))) ∧
      (∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
        (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
            𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
                (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).op).hom (γ (𝒱.face σ j) t)) ∧
      (∀ ρ : 𝒱.Idx (1 + 1),
        ∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              (p₂.preimage_mono (𝒱.inter_le_inter_face ρ j)))).op).hom (e (𝒱.face ρ j)) = 0) := by
  classical
  change (∀ t : 𝒲.Idx 1, Γ(P, 𝒲.inter t)) at c
  have : IsSeparated p₁ := isSeparated_fst fX fY p₁ p₂ hP
  have hπ : IsSeparated (p₁ ≫ fX) := inferInstance
  let := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)
  have hF : ∀ {a : ℕ} (σ : 𝒱.Idx a), IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => isAffineOpen_strip fX fY p₁ p₂ 𝒱 U hP hU σ
  let K : ∀ {a : ℕ} (σ : 𝒱.Idx a), P.OrderedAffineCoverOf (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => 𝒲.restrict (p₁ ≫ fX) (hF σ)
  have hKi : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t = 𝒲.inter t ⊓ (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => restrict_inter 𝒲 (p₁ ≫ fX) (hF σ) t
  have hBK : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ (K σ).inter t :=
    fun σ t => by rw [hKi, inf_assoc]
  have hKB : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => by rw [hKi, inf_assoc]
  have hKW : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b), (K σ).inter t ≤ 𝒲.inter t :=
    fun σ t => (hKB σ t).trans (inf_le_left.trans inf_le_left)
  have step1 : ∀ σ : 𝒱.Idx 0, ∃ g : (K σ).cochain 0,
      (K σ).d (p₁ ≫ fX) 0 g = fun t => rr (hKW σ t) (c t) := by
    intro σ
    have hmem : (fun t => rr (hKW σ t) (c t) : (K σ).cochain 1) ∈
        LinearMap.ker ((K σ).d (p₁ ≫ fX) 1) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have h0' : (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (OModulePresheaf.unit (p₁ ≫ fX)).res (𝒲.inter_le_inter_face s j) (c (𝒲.face s j))) = 0 :=
        (OModulePresheaf.d_apply (OModulePresheaf.unit (p₁ ≫ fX))
          𝒲 1 c s).symm.trans (congrFun hc s)
      have h0 : (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (𝒲.inter_le_inter_face s j) (c (𝒲.face s j))) = 0 := h0'
      have h1 := congrArg (rr (hKW σ s)) h0
      rw [map_sum, map_zero] at h1
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
      rw [map_zsmul]
      congr 1
      change rr _ (rr _ (c (𝒲.face s j))) = rr _ (rr _ (c (𝒲.face s j)))
      simp only [rr_rr]
      exact rr_rr _ _ (c (𝒲.face s j))
    obtain ⟨g, hg⟩ :=
      AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen
      (p₁ ≫ fX) (K σ) (hF σ) 0 hmem
    exact ⟨g, hg⟩
  choose g hg using step1
  let γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => rr (hBK σ t) (g σ t)
  have hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      rr (inf_le_left.trans inf_le_left) (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) (inf_le_inf_right (p₁ ⁻¹ᵁ U)
              (𝒲.inter_le_inter_face t j)))
              (γ σ (𝒲.face t j)) := by
    intro σ t
    have h1 := (Scheme.OrderedAffineCoverOf.d_apply (p₁ ≫ fX)
      (K σ) 0 (g σ) t).symm.trans (congrFun (hg σ) t)
    have h2 := congrArg (rr (hBK σ t)) h1
    rw [map_sum, rr_rr] at h2
    refine Eq.trans h2.symm (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_zsmul]
    congr 1
    change rr _ (rr _ (g σ _)) = rr _ (rr _ (g σ _))
    simp only [rr_rr]
    try rfl
  have step2 : ∀ σ : 𝒱.Idx 1, ∃ eσ : Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ),
      (K σ).aug (p₁ ≫ fX) eσ = fun t => ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        rr ((hKB σ t).trans (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
          (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))) (γ (𝒱.face σ j) t) := by
    intro σ
    set η : (K σ).cochain 0 := fun t => ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        rr ((hKB σ t).trans (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
          (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))) (γ (𝒱.face σ j) t) with hη
    have hmem : η ∈ LinearMap.ker ((K σ).d (p₁ ≫ fX) 0) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have key : ∀ j : Fin (0 + 2),
          ∑ l : Fin (0 + 2), ((-1 : ℤ) ^ (l : ℕ)) •
            rr (((K σ).inter_le_inter_face s l).trans ((hKB σ ((K σ).face s l)).trans
              (inf_le_inf_left (𝒲.inter ((K σ).face s l) ⊓ p₁ ⁻¹ᵁ U)
                (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))))
              (γ (𝒱.face σ j) (𝒲.face s l))
          = rr (hKW σ s) (c s) := by
        intro j
        have hle : (K σ).inter s ≤ 𝒲.inter s ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter (𝒱.face σ j) :=
          (hKB σ s).trans (inf_le_inf_left _ (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))
        have h3 := congrArg (rr hle) (hV (𝒱.face σ j) s)
        rw [rr_rr, map_sum] at h3
        refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h3.symm
        rw [map_zsmul]
        congr 1
        change rr _ (rr _ (g _ _)) = rr _ (rr _ (rr _ (g _ _)))
        simp only [rr_rr]
        exact rr_rr _ _ (g (𝒱.face σ j) (𝒲.face s l))
      calc
        ∑ l : Fin (0 + 2), ((-1 : ℤ) ^ (l : ℕ)) •
            rr ((K σ).inter_le_inter_face s l) (η ((K σ).face s l))
          = ∑ l : Fin (0 + 2), ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • (((-1 : ℤ) ^ (l : ℕ)) •
              rr (((K σ).inter_le_inter_face s l).trans ((hKB σ ((K σ).face s l)).trans
                (inf_le_inf_left (𝒲.inter ((K σ).face s l) ⊓ p₁ ⁻¹ᵁ U)
                  (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))))
                (γ (𝒱.face σ j) (𝒲.face s l))) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hη, map_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_zsmul, smul_comm]
            congr 2
            change rr _ (rr _ (rr _ (g (𝒱.face σ j) (𝒲.face s l)))) =
              rr _ (rr _ (g (𝒱.face σ j) (𝒲.face s l)))
            simp only [rr_rr]
            try rfl
        _ = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • rr (hKW σ s) (c s) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.smul_sum, key j]
        _ = 0 := by
            rw [Fin.sum_univ_two]
            simp
    have hrange : η ∈ LinearMap.range ((K σ).aug (p₁ ≫ fX)) := by
      rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact hmem
    obtain ⟨eσ, heσ⟩ := hrange
    exact ⟨eσ, heσ.trans hη⟩
  choose e he using step2
  have hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            rr (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              (p₂.preimage_mono (𝒱.inter_le_inter_face σ j))) (γ (𝒱.face σ j) t) := by
    intro σ t
    have h1 := (Scheme.OrderedAffineCoverOf.aug_apply (p₁ ≫ fX)
      (K σ) (e σ) t).symm.trans (congrFun (he σ) t)
    have h2 := congrArg (rr (hBK σ t)) h1
    change rr _ (rr _ (e σ)) = _ at h2
    rw [rr_rr, map_sum] at h2
    refine Eq.trans h2 (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_zsmul]
    congr 1
    change rr _ (rr _ (rr _ (g _ _))) = rr _ (rr _ (g _ _))
    simp only [rr_rr]
    try rfl
  refine ⟨γ, e, hV, hH, ?_⟩
  intro ρ
  have hbox : ∀ t : 𝒲.Idx 0,
      rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter ρ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ)
        (∑ j : Fin (1 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (inf_le_inf_left (p₁ ⁻¹ᵁ U)
            (p₂.preimage_mono (𝒱.inter_le_inter_face ρ j))) (e (𝒱.face ρ j)))
        = 0 := by
    intro t
    let G := OModulePresheaf.Leray.pullOpen p₂ fY (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
    let γt : G.cochain 𝒱 0 := fun σ => γ σ t
    have hdd := congrFun (LinearMap.congr_fun (OModulePresheaf.Leray.d_d G 𝒱 0) γt) ρ
    rw [LinearMap.comp_apply, LinearMap.zero_apply, OModulePresheaf.d_apply] at hdd
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hdd
    rw [map_zsmul, OModulePresheaf.d_apply, rr_rr]
    dsimp only [γt]
    congr 1
    have hle : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter
      (𝒱.face ρ j) :=
      inf_le_inf_left _ (p₂.preimage_mono (𝒱.inter_le_inter_face ρ j))
    have h5 := congrArg (rr hle) (hH (𝒱.face ρ j) t)
    rw [rr_rr, map_sum] at h5
    rw [map_sum]
    refine h5.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_zsmul, map_zsmul]
    congr 1
  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (K ρ)
  rw [map_zero]
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Pi.zero_apply]
  change rr ((K ρ).inter_le_base t) _ = 0
  have hfac : rr ((K ρ).inter_le_base t)
      = (rr (hKB ρ t)).comp (rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter ρ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter ρ)) := by
    ext x
    exact (rr_rr _ _ x).symm
  rw [hfac, RingHom.comp_apply, hbox t, map_zero]

end AlgebraicGeometry.OModulePresheaf
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq

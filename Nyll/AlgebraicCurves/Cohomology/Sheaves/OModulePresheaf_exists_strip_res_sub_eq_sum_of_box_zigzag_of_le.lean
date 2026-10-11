/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
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
# OModule Presheaf exists strip res sub eq sum of box zigzag of le
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace G2bStripUniqueAux

variable {P : Scheme.{u}}

/-- Restrict regular functions along an inclusion of open subsets. -/
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

end G2bStripUniqueAux

open G2bStripUniqueAux in
theorem _root_.AlgebraicGeometry.OModulePresheaf.exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (_hU : IsAffineOpen U)
    (γ : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U) (𝒲.inter_le_inter_face t j)))).op).hom (γ σ (𝒲.face t
                j)))
    (hH : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
              (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).op).hom
                (γ (𝒱.face σ j) t))
    (U' : X.Opens) (hU' : IsAffineOpen U') (hle : U' ≤ U)
    (γ' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx 0), Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (e' : ∀ σ : 𝒱.Idx 1, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ))
    (hV' : ∀ (σ : 𝒱.Idx 0) (t : 𝒲.Idx (0 + 1)),
      (P.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t)).op).hom (c t)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
              (inf_le_inf_right (p₁ ⁻¹ᵁ U') (𝒲.inter_le_inter_face t j)))).op).hom (γ' σ (𝒲.face t
                j)))
    (hH' : ∀ (σ : 𝒱.Idx (0 + 1)) (t : 𝒲.Idx 0),
      (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e' σ)
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U')
              (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).op).hom
                (γ' (𝒱.face σ j) t)) :
    ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ)
          (p₁.preimage_mono (hle)) : p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ p₁
            ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ)).op).hom (e σ) - e' σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U')
              (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j)) := by
  classical
  change (∀ t : 𝒲.Idx 1, Γ(P, 𝒲.inter t)) at c
  have : IsSeparated p₁ := isSeparated_fst fX fY p₁ p₂ hP
  have hπ : IsSeparated (p₁ ≫ fX) := inferInstance
  let := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)
  have hF : ∀ {a : ℕ} (σ : 𝒱.Idx a), IsAffineOpen (p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => isAffineOpen_strip fX fY p₁ p₂ 𝒱 U' hP hU' σ
  let K : ∀ {a : ℕ} (σ : 𝒱.Idx a), P.OrderedAffineCoverOf (p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ => 𝒲.restrict (p₁ ≫ fX) (hF σ)
  have hKi : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t = 𝒲.inter t ⊓ (p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ) :=
    fun σ t => restrict_inter 𝒲 (p₁ ≫ fX) (hF σ) t
  have hKB' : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => by rw [hKi, inf_assoc]
  have hB'K : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ (K σ).inter t :=
    fun σ t => by rw [hKi, inf_assoc]
  have hB'B : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      𝒲.inter t ⊓ p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => inf_le_inf_right _ (inf_le_inf_left _ (p₁.preimage_mono hle))
  have hKB : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b),
      (K σ).inter t ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter σ :=
    fun σ t => (hKB' σ t).trans (hB'B σ t)
  have hKW : ∀ {a b : ℕ} (σ : 𝒱.Idx a) (t : 𝒲.Idx b), (K σ).inter t ≤ 𝒲.inter t :=
    fun σ t => (hKB' σ t).trans (inf_le_left.trans inf_le_left)
  have step1 : ∀ i : 𝒱.Idx 0, ∃ gi : Γ(P, p₁ ⁻¹ᵁ U' ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      (K i).aug (p₁ ≫ fX) gi = fun t => rr (hKB i t) (γ i t) - rr (hKB' i t) (γ' i t) := by
    intro i
    set δ : (K i).cochain 0 := fun t => rr (hKB i t) (γ i t) - rr (hKB' i t) (γ' i t) with hδ
    have hmem : δ ∈ LinearMap.ker ((K i).d (p₁ ≫ fX) 0) := by
      rw [LinearMap.mem_ker]
      funext s
      rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
      have h1 := congrArg (rr (hKB i s)) (hV i s)
      have h1' := congrArg (rr (hKB' i s)) (hV' i s)
      rw [rr_rr, map_sum] at h1 h1'
      have h2 : rr ((hKB i s).trans (inf_le_left.trans inf_le_left)) (c s)
          = rr ((hKB' i s).trans (inf_le_left.trans inf_le_left)) (c s) := rfl
      calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • rr ((K i).inter_le_inter_face s j) (δ ((K
        i).face s j))
          = ∑ j : Fin (0 + 2), rr (hKB i s) (((-1 : ℤ) ^ (j : ℕ)) •
              rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter i) (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face s j)))
                (γ i (𝒲.face s j)))
            - ∑ j : Fin (0 + 2), rr (hKB' i s) (((-1 : ℤ) ^ (j : ℕ)) •
              rr (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter i) (inf_le_inf_right (p₁ ⁻¹ᵁ U')
                (𝒲.inter_le_inter_face s j)))
                (γ' i (𝒲.face s j))) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hδ, map_sub, smul_sub, map_zsmul, map_zsmul]
            congr 2
            · change rr _ (rr _ (γ _ _)) = rr _ (rr _ (γ _ _))
              simp only [rr_rr]
              try rfl
            · change rr _ (rr _ (γ' _ _)) = rr _ (rr _ (γ' _ _))
              simp only [rr_rr]
              try rfl
        _ = 0 := by rw [← h1, ← h1', h2, sub_self]
    have hrange : δ ∈ LinearMap.range ((K i).aug (p₁ ≫ fX)) := by
      rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact hmem
    obtain ⟨gi, hgi⟩ := hrange
    exact ⟨gi, hgi.trans hδ⟩
  choose g hg using step1
  refine ⟨g, fun σ => ?_⟩
  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (K σ)
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Scheme.OrderedAffineCoverOf.aug_apply, map_sub,
    map_sum]
  change rr _ (rr _ (e σ)) - rr _ (e' σ) = ∑ j : Fin (0 + 2), rr _ (((-1 : ℤ) ^ (j : ℕ)) • rr _ (g
    (𝒱.face σ j)))
  have hHt := congrArg (rr (hKB σ t)) (hH σ t)
  have hHt' := congrArg (rr (hKB' σ t)) (hH' σ t)
  rw [rr_rr, map_sum] at hHt hHt'
  rw [rr_rr, hHt, hHt', ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, map_zsmul, ← smul_sub]
  congr 1
  have hKK : (K σ).inter t ≤ (K (𝒱.face σ j)).inter t := by
    exact (hKi σ t).le.trans ((inf_le_inf_left _
      (inf_le_inf_left _ (p₂.preimage_mono (𝒱.inter_le_inter_face σ j)))).trans
        (hKi (𝒱.face σ j) t).ge)
  have h3 := congrArg (rr hKK)
    ((Scheme.OrderedAffineCoverOf.aug_apply (p₁ ≫ fX) (K (𝒱.face σ j)) (g (𝒱.face σ j))
      t).symm.trans
      (congrFun (hg (𝒱.face σ j)) t))
  change rr hKK (rr _ (g _)) = rr hKK (rr _ (γ _ _) - rr _ (γ' _ _)) at h3
  rw [rr_rr, map_sub, rr_rr, rr_rr] at h3
  change rr _ (rr _ (γ _ _)) - rr _ (rr _ (γ' _ _)) = rr _ (rr _ (g _))
  rw [rr_rr, rr_rr, rr_rr]
  exact h3.symm
end OModulePresheaf_exists_strip_res_sub_eq_sum_of_box_zigzag_of_le
end AlgebraicCurves.Cohomology.Sheaves.Proofs
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

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Opposites
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Category.TopCat.Opens
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverOf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_aug_injective

/-!
# OModule Presheaf exists res eq sum of box zigzag of exists strip eq sum
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace G2aBody

section Res
variable {P : Scheme.{u}}

theorem res_res {U V W : P.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(P, U)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom x)
      = (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end Res

section Cover

variable {k : Type u} [Field k] {X Y P : Scheme.{u}}
  (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
  [IsSeparated fX] [IsSeparated fY]
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
  (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
  (U : X.Opens) (hU : IsAffineOpen U)

/-- The affine cover of an intersection strip obtained from the cover of `Y`. -/
noncomputable def boxCover {n : ℕ} (t : 𝒲.Idx n) : P.OrderedAffineCoverOf (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U)
  where
  ι := 𝒱.ι
  U i := (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) ⊓ p₂ ⁻¹ᵁ 𝒱.U i
  isAffineOpen i := by
    have : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
    have : IsSeparated (p₁ ≫ fX) := inferInstance
    have h1 : IsAffineOpen (𝒲.inter t) := Scheme.OrderedAffineCover.isAffineOpen_inter (p₁ ≫ fX) 𝒲 t
    have h2 : IsAffineOpen (𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) :=
      Scheme.OrderedAffineCover.fiberAffineOpen p₁ fX h1 hU
    exact Scheme.OrderedAffineCover.fiberAffineOpen p₂ fY h2 (𝒱.isAffineOpen i)
  le _ := inf_le_left
  iSup_eq := by
    rw [← inf_iSup_eq, ← Scheme.Hom.preimage_iSup, 𝒱.iSup_eq_top]
    exact le_antisymm inf_le_left (le_inf le_rfl le_top)

variable {fX fY p₁ p₂ 𝒲 𝒱 U}

theorem boxCover_face {n m : ℕ} (t : 𝒲.Idx n) (σ : 𝒱.Idx (m + 1)) (j : Fin (m + 2)) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).face σ j = 𝒱.face σ j := rfl

theorem inter_le_box {n m : ℕ} (t : 𝒲.Idx n) (s : 𝒱.Idx m) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s := by
  refine le_inf (((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s 0).trans inf_le_left) ?_
  calc (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ ⨅ j, p₂ ⁻¹ᵁ 𝒱.U (s.1 j) :=
        le_iInf fun j => ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s j).trans inf_le_right
    _ = p₂ ⁻¹ᵁ 𝒱.inter s := (Scheme.OrderedAffineCover.preimage_iInf_fin p₂ _).symm

theorem box_le_inter {n m : ℕ} (t : 𝒲.Idx n) (s : 𝒱.Idx m) :
    𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s :=
  le_iInf fun j => le_inf inf_le_left (inf_le_right.trans (p₂.preimage_mono (𝒱.inter_le s j)))

theorem inter_le_inter {n n' m : ℕ} (t : 𝒲.Idx n) (t' : 𝒲.Idx n') (h : 𝒲.inter t ≤ 𝒲.inter t')
    (s : 𝒱.Idx m) :
    (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t').inter s :=
  le_iInf fun j => ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter_le s j).trans
    (inf_le_inf_right _ (inf_le_inf_right _ h))

end Cover

end G2aBody

open G2aBody in
theorem
  _root_.AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [IsSeparated fX] [IsSeparated fY]
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (𝒲 : P.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (U : X.Opens) (hU : IsAffineOpen U)
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
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (γ (𝒱.face σ j) t))
    (he : ∃ g : ∀ i : 𝒱.Idx 0, Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter i),
      ∀ σ : 𝒱.Idx (0 + 1), e σ
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
            (P.presheaf.map (homOfLE (inf_le_inf_left (p₁ ⁻¹ᵁ U)
              ((TopologicalSpace.Opens.map p₂.base).monotone (𝒱.inter_le_inter_face σ j)))).op).hom
                (g (𝒱.face σ j))) :
    ∃ β : ∀ t : 𝒲.Idx 0, Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      ∀ t : 𝒲.Idx (0 + 1),
        (P.presheaf.map (homOfLE (inf_le_left : 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ≤ 𝒲.inter t)).op).hom (c t)
          = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
              (P.presheaf.map (homOfLE (inf_le_inf_right (p₁ ⁻¹ᵁ U)
                (𝒲.inter_le_inter_face t j))).op).hom (β (𝒲.face t j)) := by
  classical
  change (∀ t : 𝒲.Idx 1, Γ(P, 𝒲.inter t)) at c
  obtain ⟨g, hg⟩ := he
  have : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip inferInstance
  have : IsSeparated (p₁ ≫ fX) := inferInstance
  let := Scheme.OrderedAffineCoverOf.moduleSections (p₁ ≫ fX)
  let f : ∀ t : 𝒲.Idx 0, (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).cochain 0 := fun t s =>
    (P.presheaf.map (homOfLE (inter_le_box hP hU t s)).op).hom
      (γ s t - (P.presheaf.map (homOfLE (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right :
          𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s)).op).hom (g s))
  have hf : ∀ t : 𝒲.Idx 0, (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).d (p₁ ≫ fX) 0 (f t) = 0 := by
    intro t
    funext σ
    rw [Scheme.OrderedAffineCoverOf.d_apply]
    change 𝒱.Idx 1 at σ
    have h1 := congrArg (fun x => (P.presheaf.map (homOfLE
      (inter_le_box hP hU t σ)).op).hom x) (hH σ t)
    have h2 := congrArg (fun x => (P.presheaf.map (homOfLE
      ((inter_le_box hP hU t σ).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter σ) inf_le_right))).op).hom
        x) (hg σ)
    simp only [map_sum, map_zsmul, map_sub, res_res, f] at h1 h2 ⊢
    rw [Fin.sum_univ_two] at h1 h2 ⊢
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h1 h2 ⊢
    simp only [boxCover_face] at h1 h2 ⊢
    change _ = (0 : Γ(P, _))
    linear_combination h2 - h1
  have hglue : ∀ t : 𝒲.Idx 0, ∃ w : Γ(P, 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U),
      (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).aug (p₁ ≫ fX) w = f t := by
    intro t
    have hmem : f t ∈ LinearMap.range ((boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).aug (p₁ ≫ fX)) := by
      rw [← Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
      exact LinearMap.mem_ker.mpr (hf t)
    exact LinearMap.mem_range.mp hmem
  choose β hβ using hglue
  have hβ' : ∀ (t : 𝒲.Idx 0) (s : 𝒱.Idx 0) {O : P.Opens}
      (h : O ≤ (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t).inter s)
      (h₁ : O ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U) (h₂ : O ≤ 𝒲.inter t ⊓ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s)
      (h₃ : O ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ 𝒱.inter s),
      (P.presheaf.map (homOfLE h₁).op).hom (β t)
        = (P.presheaf.map (homOfLE h₂).op).hom (γ s t) - (P.presheaf.map (homOfLE h₃).op).hom (g s)
          := by
    intro t s O h h₁ h₂ h₃
    have hbcalc := (Scheme.OrderedAffineCoverOf.aug_apply (p₁ ≫ fX)
      (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t) (β t) s).symm.trans (congrFun (hβ t) s)
    have := congrArg (fun x => (P.presheaf.map (homOfLE h).op).hom x) hbcalc
    simp only [map_sub, res_res, f] at this
    exact this
  refine ⟨β, fun t => ?_⟩
  apply Scheme.OrderedAffineCoverOf.aug_injective (p₁ ≫ fX) (boxCover fX fY p₁ p₂ hP 𝒲 𝒱 U hU t)
  funext s
  simp only [Scheme.OrderedAffineCoverOf.aug_apply, map_sum, map_zsmul, res_res]
  have h3 := congrArg (fun x => (P.presheaf.map (homOfLE (inter_le_box hP hU t s)).op).hom x) (hV s
    t)
  simp only [map_sum, map_zsmul, res_res] at h3
  rw [Fin.sum_univ_two] at h3 ⊢
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h3 ⊢
  have l0 := inter_le_inter hP hU t (𝒲.face t 0) (𝒲.inter_le_inter_face t 0) s
  have l1 := inter_le_inter hP hU t (𝒲.face t 1) (𝒲.inter_le_inter_face t 1) s
  rw [hβ' (𝒲.face t 0) s l0 _ (l0.trans (inter_le_box hP hU _ s))
      ((inter_le_box hP hU t s).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right)),
    hβ' (𝒲.face t 1) s l1 _ (l1.trans (inter_le_box hP hU _ s))
      ((inter_le_box hP hU t s).trans (inf_le_inf_right (p₂ ⁻¹ᵁ 𝒱.inter s) inf_le_right))]
  linear_combination h3
end OModulePresheaf_exists_res_eq_sum_of_box_zigzag_of_exists_strip_eq_sum
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
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
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
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U

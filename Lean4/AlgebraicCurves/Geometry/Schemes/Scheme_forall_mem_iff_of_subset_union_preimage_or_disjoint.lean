/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.ProjectivePresentation
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Schemes.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton

/-!
# Scheme forall mem iff of subset union preimage or disjoint
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TranslateCore
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
  [GrpObj (Over.mk t)]

/-- Right translation by the chosen section in the category of schemes over the base. -/
noncomputable def T (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : Over.mk t ⟶ Over.mk t
  :=
  𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)

/-- Left translation by the chosen section composed with inversion in the group object. -/
noncomputable def S (c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : Over.mk t ⟶ Over.mk t
  :=
  (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ c) * (𝟙 (Over.mk t))⁻¹

/-- The underlying point of the scheme determined by a section over the base field. -/
noncomputable def P (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : X :=
  y.left.base (IsLocalRing.closedPoint k)

variable {t}

omit [GrpObj (Over.mk t)] in
lemma toUnit_pt_comp (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ a = a := by
  rw [show CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ from
    Subsingleton.elim _ _]
  exact Category.id_comp a

lemma pt_comp_T (y a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : y ≫ T t a = y * a := by
  unfold T
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    SemiCartesianMonoidalCategory.comp_toUnit,
    toUnit_pt_comp]

lemma pt_comp_S (y c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : y ≫ S t c = c * y⁻¹ :=
  by
  unfold S
  rw [MonObj.comp_mul, ← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit, toUnit_pt_comp,
    GrpObj.comp_inv, Category.comp_id]

lemma T_comp_T (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : T t a ≫ T t b = T t (a *
  b) := by
  unfold T
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    SemiCartesianMonoidalCategory.comp_toUnit,
    show CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b) =
      (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a) * (CartesianMonoidalCategory.toUnit
        (Over.mk t) ≫ b) from
      MonObj.comp_mul _ _ _, mul_assoc]

lemma T_one : T t (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) = 𝟙 (Over.mk t) := by
  unfold T
  rw [show CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of
    k))) ⟶ Over.mk t) =
      (1 : Over.mk t ⟶ Over.mk t) from MonObj.comp_one _, mul_one]

lemma S_comp_S [IsCommMonObj (Over.mk t)] (c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    S t c ≫ S t c = 𝟙 (Over.mk t) := by
  have h1 : S t c ≫ S t c = (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ c) * (S t c)⁻¹ := by
    conv_lhs => rw [show S t c ≫ S t c = S t c ≫ ((CartesianMonoidalCategory.toUnit (Over.mk t) ≫
      c) *
      (𝟙 (Over.mk t))⁻¹) from rfl]
    rw [MonObj.comp_mul, ← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit,
      GrpObj.comp_inv,
      Category.comp_id]
  rw [h1]
  unfold S
  rw [mul_inv_rev, inv_inv, mul_comm (𝟙 (Over.mk t)) _, ← mul_assoc, mul_inv_cancel, one_mul]

scoped instance isIso_T (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : IsIso (T t a) :=
  ⟨⟨T t a⁻¹, by rw [T_comp_T, mul_inv_cancel, T_one], by rw [T_comp_T, inv_mul_cancel, T_one]⟩⟩

scoped instance isIso_S [IsCommMonObj (Over.mk t)] (c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
  Over.mk t) :
    IsIso (S t c) :=
  ⟨⟨S t c, S_comp_S c, S_comp_S c⟩⟩

omit [GrpObj (Over.mk t)] in
lemma P_comp (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) (φ : Over.mk t ⟶ Over.mk t) :
    P t (y ≫ φ) = φ.left.base (P t y) := rfl

lemma T_base_P (y a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    (T t a).left.base (P t y) = P t (y * a) := by
  rw [← P_comp, pt_comp_T]

lemma S_base_P (y c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    (S t c).left.base (P t y) = P t (c * y⁻¹) := by
  rw [← P_comp, pt_comp_S]
omit [GrpObj (Over.mk t)] in
lemma surjective_left_base (φ : Over.mk t ⟶ Over.mk t) [IsIso φ] : Function.Surjective φ.left.base
  := by
  have : IsIso φ.left := (inferInstance : IsIso ((Over.forget _).map φ))
  exact (ConcreteCategory.bijective_of_isIso φ.left.base).2
omit [GrpObj (Over.mk t)] in
lemma compl_preimage (φ : Over.mk t ⟶ Over.mk t) [IsIso φ] {D : Set X} (hD : IsClosed D) (hD' : D ≠
  Set.univ) :
    IsOpen (φ.left.base ⁻¹' D)ᶜ ∧ ((φ.left.base ⁻¹' D)ᶜ).Nonempty := by
  refine ⟨(hD.preimage φ.left.continuous).isOpen_compl, ?_⟩
  obtain ⟨x₀, hx₀⟩ := (Set.ne_univ_iff_exists_notMem D).mp hD'
  obtain ⟨x, rfl⟩ := surjective_left_base φ x₀
  exact ⟨x, hx₀⟩

section main

variable [IsAlgClosed k] [LocallyOfFiniteType t] [IsIntegral X] [IsCommMonObj (Over.mk t)]

omit [GrpObj (Over.mk t)] [IsIntegral X] [IsCommMonObj (Over.mk t)] in
lemma exists_P_mem {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t, P t b ∈ U := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t
  have hdense : Dense (closedPoints X) := by
    rw [dense_iff_closure_eq]
    simpa using JacobsonSpace.closure_inter_closedPoints (X := X) (Z := Set.univ) isClosed_univ
  obtain ⟨x, hxU, hxcl⟩ := hdense.inter_open_nonempty U hU hne
  obtain ⟨b, hb⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t x hxcl
  refine ⟨b, ?_⟩
  change b.left.base (IsLocalRing.closedPoint k) ∈ U
  rw [hb]
  exact hxU

lemma key {D : Set X} (hD : IsClosed D) (hD' : D ≠ Set.univ) {Z : Set X} (_hZ' : IsIrreducible Z)
    (h : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Z ⊆ ((T t a).left.base ⁻¹' D ∪ (T t b).left.base ⁻¹' D ∪ (T t (a * b)⁻¹).left.base ⁻¹' D) ∨
      Disjoint Z ((T t a).left.base ⁻¹' D ∪ (T t b).left.base ⁻¹' D ∪ (T t (a * b)⁻¹).left.base ⁻¹'
        D))
    (z z' d : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) (hz : P t z ∈ Z) (hz' : P t z' ∈ Z)
    (hd : P t d ∈ D) : P t (d * (z⁻¹ * z')) ∈ D := by
  have hirr : IrreducibleSpace X := inferInstance
  have hpre : PreirreducibleSpace X := inferInstance
  let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := z⁻¹ * d
  have hza : z * a = d := mul_inv_cancel_left z d
  let c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := z' * a⁻¹
  obtain ⟨hU₁, hne₁⟩ := compl_preimage (T t z') hD hD'
  obtain ⟨hU₂, hne₂⟩ := compl_preimage (S t c) hD hD'
  obtain ⟨b, hb⟩ := exists_P_mem (t := t) (hU₁.inter hU₂)
    (@nonempty_preirreducible_inter _ _ _ _ hpre hU₁ hU₂ hne₁ hne₂)
  have hb₁ : (T t z').left.base (P t b) ∉ D := hb.1
  have hb₂ : (S t c).left.base (P t b) ∉ D := hb.2
  rw [T_base_P] at hb₁
  rw [S_base_P] at hb₂
  have hzmem : P t z ∈ (T t a).left.base ⁻¹' D ∪ (T t b).left.base ⁻¹' D ∪ (T t (a *
    b)⁻¹).left.base ⁻¹' D := by
    left; left
    change (T t a).left.base (P t z) ∈ D
    rw [T_base_P, hza]
    exact hd
  have hsub := (h a b).resolve_right fun hdis => Set.disjoint_left.mp hdis hz hzmem
  rcases hsub hz' with (h1 | h2) | h3
  · have e : z' * a = d * (z⁻¹ * z') := by
      simp only [a]
      rw [mul_left_comm, mul_comm z' d, mul_left_comm]
    have h1' : (T t a).left.base (P t z') ∈ D := h1
    rw [T_base_P, e] at h1'
    exact h1'
  · exfalso
    have h2' : (T t b).left.base (P t z') ∈ D := h2
    rw [T_base_P, mul_comm] at h2'
    exact hb₁ h2'
  · exfalso
    have h3' : (T t (a * b)⁻¹).left.base (P t z') ∈ D := h3
    rw [T_base_P] at h3'
    have e : z' * (a * b)⁻¹ = c * b⁻¹ := by
      simp only [c]
      rw [mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_assoc]
    rw [e] at h3'
    exact hb₂ h3'

theorem main (D : Set X) (hD : IsClosed D) (hD' : D ≠ Set.univ) (Z : Set X) (_hZ : IsClosed Z)
    (hZ' : IsIrreducible Z)
    (h : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Z ⊆ ((T t a).left.base ⁻¹' D ∪ (T t b).left.base ⁻¹' D ∪ (T t (a * b)⁻¹).left.base ⁻¹' D) ∨
      Disjoint Z ((T t a).left.base ⁻¹' D ∪ (T t b).left.base ⁻¹' D ∪ (T t (a * b)⁻¹).left.base ⁻¹'
        D))
    (z z' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) (hz : P t z ∈ Z) (hz' : P t z' ∈ Z)
    (d : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    P t d ∈ D ↔ P t (d * (z⁻¹ * z')) ∈ D := by
  refine ⟨key hD hD' hZ' h z z' d hz hz', fun hd => ?_⟩
  have := key hD hD' hZ' h z' z (d * (z⁻¹ * z')) hz' hz hd
  have e : d * (z⁻¹ * z') * (z'⁻¹ * z) = d := by group
  rwa [e] at this

end main

end AlgebraicGeometry.Scheme.TranslateCore

theorem _root_.AlgebraicGeometry.Scheme.forall_mem_iff_of_subset_union_preimage_or_disjoint
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] [IsIntegral X] [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (D : Set X) (hD : IsClosed D) (hD' : D ≠ Set.univ) (Z : Set X) (hZ : IsClosed Z) (hZ' :
      IsIrreducible Z)
    (h : ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Z ⊆ ((𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base
              ⁻¹' D) ∨
      Disjoint Z ((𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base
        ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹' D ∪
            (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base
              ⁻¹' D))
    (z z' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t)
    (hz : z.left.base (IsLocalRing.closedPoint k) ∈ Z) (hz' : z'.left.base (IsLocalRing.closedPoint
      k) ∈ Z)
    (d : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    d.left.base (IsLocalRing.closedPoint k) ∈ D ↔ (d * (z⁻¹ * z')).left.base
      (IsLocalRing.closedPoint k) ∈ D :=
  AlgebraicGeometry.Scheme.TranslateCore.main D hD hD' Z hZ hZ' h z z' hz hz' d
end Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

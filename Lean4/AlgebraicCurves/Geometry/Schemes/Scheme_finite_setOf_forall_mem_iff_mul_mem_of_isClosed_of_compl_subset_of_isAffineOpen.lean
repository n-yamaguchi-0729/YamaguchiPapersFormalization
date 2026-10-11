/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.JacobsonSpace

/-!
# Scheme finite set Of forall mem iff mul mem of is Closed of compl subset of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open scoped CategoryTheory.MonObj

noncomputable section

namespace P2mThetaFinB

variable {k : Type u} [Field k] {X : Scheme.{u}} {t : X ⟶ Spec (CommRingCat.of k)}

/-- The rational points of the scheme over the base field, expressed as morphisms over its
spectrum. -/
abbrev Pt (t : X ⟶ Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

/-- The underlying scheme point of a rational point, evaluated at the unique point of the base
spectrum. -/
def pt (z : Pt t) : X := z.left (IsLocalRing.closedPoint k)

lemma left_comp (z : Pt t) : (z.left : Spec (CommRingCat.of k) ⟶ X) ≫ t = 𝟙 _ := Over.w z

lemma pt_injective [LocallyOfFiniteType t] [IsAlgClosed k] : Function.Injective (pt (t := t)) :=
  fun z z' h => Over.OverMorphism.ext
    (ext_of_apply_closedPoint_eq (X := X) (f := z.left) (g := z'.left) t (left_comp z)
      (left_comp z') h)

lemma exists_pt_eq [LocallyOfFiniteType t] [IsAlgClosed k] {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ z : Pt t, pt z = y :=
  ⟨Over.homMk (pointOfClosedPoint (X := X) t y hy) (by simp), pointOfClosedPoint_apply t y hy _⟩

section Grp

variable [GrpObj (Over.mk t)]

/-- Left translation by a rational point of the group scheme. -/
def lmul (z : Pt t) : Over.mk t ⟶ Over.mk t :=
  (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z) * 𝟙 (Over.mk t)

lemma comp_lmul (x z : Pt t) : x ≫ lmul z = z * x := by
  have h1 : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ z = z := by
    rw [show CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ from
      Subsingleton.elim _ _]
    exact Category.id_comp z
  rw [lmul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.comp_toUnit, h1]

lemma pt_mul (z x : Pt t) : pt (z * x) = (lmul z).left (pt x) := by
  rw [← comp_lmul]
  rfl

/-- The underlying scheme morphism of inversion in the group scheme. -/
def invLeft (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] : X ⟶ X :=
  (ι[Over.mk t]).left

lemma pt_inv (x : Pt t) : pt x⁻¹ = invLeft t (pt x) := by
  rw [Hom.inv_def]
  rfl

/-- The intersection of the inverse images of `Z` under left translation by its rational points. -/
def Cplus (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] (Z : Set X) : Set X :=
  ⋂ z ∈ {z : Pt t | pt z ∈ Z}, ((lmul z).left : X ⟶ X) ⁻¹' Z

lemma isClosed_Cplus {Z : Set X} (hZ : IsClosed Z) : IsClosed (Cplus t Z) :=
  isClosed_biInter fun z _ => hZ.preimage (lmul z).left.continuous

lemma mem_Cplus_iff {Z : Set X} (x : Pt t) :
    pt x ∈ Cplus t Z ↔ ∀ z : Pt t, pt z ∈ Z → pt (z * x) ∈ Z := by
  simp only [Cplus, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage, pt_mul]

/-- The closed-set candidate for the rational stabilizer of `Z`, imposing preservation under an
element and its inverse. -/
def C (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] (Z : Set X) : Set X :=
  Cplus t Z ∩ (invLeft t) ⁻¹' Cplus t Z

lemma isClosed_C {Z : Set X} (hZ : IsClosed Z) : IsClosed (C t Z) :=
  (isClosed_Cplus hZ).inter ((isClosed_Cplus hZ).preimage (invLeft t).continuous)

lemma mem_stab_iff {Z : Set X} (x : Pt t) :
    (∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z) ↔ pt x ∈ C t Z := by
  rw [C, Set.mem_inter_iff, Set.mem_preimage, ← pt_inv, mem_Cplus_iff, mem_Cplus_iff]
  constructor
  · intro h
    refine ⟨fun z hz => (h z).1 hz, fun z hz => ?_⟩
    have := (h (z * x⁻¹)).2
    rw [inv_mul_cancel_right] at this
    exact this hz
  · rintro ⟨h₁, h₂⟩ z
    refine ⟨h₁ z, fun hz => ?_⟩
    have := h₂ (z * x) hz
    rwa [mul_inv_cancel_right] at this

end Grp

variable (t) in
lemma finite_of_isClosed_of_subset_affineOpen [IsProper t] {C : Set X} (hC : IsClosed C)
    {U : X.Opens} (hU : IsAffineOpen U) (hCU : C ⊆ U) : C.Finite := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩
  have hrange : Set.range I.subschemeι = C := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨C, hC⟩
  have htop : I.subschemeι ⁻¹ᵁ U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact hCU (hrange ▸ Set.mem_range_self y)
  have hAff : IsAffine I.subscheme := by
    have h1 : IsAffineOpen (I.subschemeι ⁻¹ᵁ U) := hU.preimage I.subschemeι
    rw [htop] at h1
    have : IsAffine (⊤ : I.subscheme.Opens) := h1
    exact IsAffine.of_isIso I.subscheme.topIso.inv
  have hfin : IsFinite (I.subschemeι ≫ t) := by
    rw [IsFinite.iff_isProper_and_isAffineHom]
    exact ⟨inferInstance, isAffineHom_of_isAffine _⟩
  have huniv : (Set.univ : Set I.subscheme).Finite := by
    have := (I.subschemeι ≫ t).finite_preimage_singleton (IsLocalRing.closedPoint k)
    refine this.subset fun y _ => ?_
    simp only [Set.mem_preimage]
    exact Subsingleton.elim _ _
  rw [← hrange, ← Set.image_univ]
  exact huniv.image _

theorem main [IsAlgClosed k] [IsProper t] [GrpObj (Over.mk t)] (Z : Set X) (hZ : IsClosed Z) (U :
  X.Opens)
    (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ U) (he : pt (1 : Pt t) ∉ Z) :
    Set.Finite {x : Pt t | ∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z} := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t
  have hS : {x : Pt t | ∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z} = pt ⁻¹' C t Z := by
    ext x
    exact mem_stab_iff x
  rw [hS]
  have hCZ : C t Z ⊆ U := by
    intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := by
      by_contra hyZ
      exact hyU (hZU hyZ)
    have hcl : IsClosed (C t Z ∩ Z) := (isClosed_C hZ).inter hZ
    have hne : (C t Z ∩ Z ∩ closedPoints X).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := JacobsonSpace.closure_inter_closedPoints_eq_closure hcl.isLocallyClosed
      rw [hemp, closure_empty, hcl.closure_eq] at this
      exact (this ▸ (Set.mem_empty_iff_false y)).mp ⟨hy, hyZ⟩
    obtain ⟨y₀, ⟨hy₀C, hy₀Z⟩, hy₀cl⟩ := hne
    obtain ⟨z₀, rfl⟩ := exists_pt_eq (t := t) (mem_closedPoints_iff.mp hy₀cl)
    have hst := (mem_stab_iff z₀).2 hy₀C 1
    rw [one_mul] at hst
    exact he (hst.2 hy₀Z)
  have hCfin : (C t Z).Finite := finite_of_isClosed_of_subset_affineOpen t (isClosed_C hZ) hU hCZ
  exact hCfin.preimage pt_injective.injOn

end P2mThetaFinB

end

end Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen in
open _root_.CategoryTheory in
open _root_.CategoryTheory.Limits in
open _root_.CategoryTheory.MonoidalCategory in
open _root_.AlgebraicGeometry in
open scoped CategoryTheory.MonObj in
theorem finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [GrpObj (Over.mk t)]
    (Z : Set X) (hZ : IsClosed Z) (U : X.Opens) (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ (U : Set X))
    (he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t).left (IsLocalRing.closedPoint k)
      ∉ Z) :
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
      ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        z.left (IsLocalRing.closedPoint k) ∈ Z ↔ (z * x).left (IsLocalRing.closedPoint k) ∈ Z} :=
  P2mThetaFinB.main Z hZ U hU hZU he
end AlgebraicGeometry.Scheme
end ProofImplementation

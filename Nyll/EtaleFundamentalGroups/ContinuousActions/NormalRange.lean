/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ProCGroups.ProC.Quotients.LeftQuotientProjectionSections
import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
import Nyll.EtaleFundamentalGroups.ContinuousActions.FiniteLimitsAndColimits
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Normal ranges detected by finite continuous actions

The range of a continuous homomorphism of profinite groups is normal exactly
when, on every transitive finite continuous action of the target, one point
fixed by the range forces every point to be fixed by the range.

This is the group-action statement underlying
[Stacks Project, Tag 0BTS](https://stacks.math.columbia.edu/tag/0BTS).
-/

noncomputable section

universe g'' g' w

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.ContAction

variable {G'' : Type g''} [Group G''] [TopologicalSpace G'']
  [CompactSpace G'']
variable {G' : Type g'} [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G'] [CompactSpace G'] [T2Space G']
  [TotallyDisconnectedSpace G']

omit [CompactSpace G''] [IsTopologicalGroup G'] [CompactSpace G'] [T2Space G']
  [TotallyDisconnectedSpace G'] in
private theorem fixed_point_implies_trivial_of_range_normal
    (h : G'' →ₜ* G') (hnormal : h.toMonoidHom.range.Normal)
    (X : ContAction FintypeCat.{w} G')
    (htrans : MulAction.IsPretransitive G' X.obj.V)
    (hfixed : ∃ x : X.obj.V, ∀ a : G'', h a • x = x) :
    ∀ (a : G'') (x : X.obj.V), h a • x = x := by
  let : h.toMonoidHom.range.Normal := hnormal
  obtain ⟨x, hx⟩ := hfixed
  have hxrange :
      x ∈ MulAction.fixedPoints h.toMonoidHom.range X.obj.V := by
    rintro ⟨_, ⟨a, rfl⟩⟩
    exact hx a
  intro a y
  obtain ⟨g, rfl⟩ := htrans.exists_smul_eq x y
  have hgy :
      g • x ∈ MulAction.fixedPoints h.toMonoidHom.range X.obj.V :=
    smul_mem_fixedPoints_of_normal g hxrange
  exact hgy ⟨h a, ⟨a, rfl⟩⟩

private theorem range_normal_of_fixed_point_implies_trivial
    (h : G'' →ₜ* G')
    (hfixed :
      ∀ X : ContAction FintypeCat.{w} G',
        MulAction.IsPretransitive G' X.obj.V →
        (∃ x : X.obj.V, ∀ a : G'', h a • x = x) →
        ∀ (a : G'') (x : X.obj.V), h a • x = x) :
    h.toMonoidHom.range.Normal := by
  constructor
  intro n hn g
  obtain ⟨a, rfl⟩ := hn
  by_contra hconj
  let K : ClosedSubgroup G' :=
    { toSubgroup := h.toMonoidHom.range
      isClosed' := ProCGroups.ContinuousMonoidHom.isClosed_range h }
  have hconjK : g * h a * g⁻¹ ∉ (K : Set G') := by
    intro hmem
    exact hconj hmem
  obtain ⟨U, hKU, hconjU⟩ :=
    ProCGroups.ProC.exists_openSubgroup_ge_closedSubgroup_not_mem
      K hconjK
  let : Finite (G' ⧸ (U : Subgroup G')) :=
    Subgroup.quotient_finite_of_isOpen (U : Subgroup G') U.isOpen'
  let hex := Finite.exists_equiv_fin (G' ⧸ (U : Subgroup G'))
  let n : ℕ := hex.choose
  let qEquiv : (G' ⧸ (U : Subgroup G')) ≃ Fin n :=
    Classical.choice hex.choose_spec
  let A := ULift.{w} (Fin n)
  let e : A ≃ (G' ⧸ (U : Subgroup G')) :=
    Equiv.ulift.trans qEquiv.symm
  let : MulAction G' A := e.mulAction G'
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have stabilizer_A_eq (x : A) :
      MulAction.stabilizer G' x =
        MulAction.stabilizer G' (e x) := by
    ext s
    simp only [MulAction.mem_stabilizer_iff, Equiv.smul_def,
      Equiv.symm_apply_eq]
  have hAcont : ContinuousSMul G' A := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    rw [stabilizer_A_eq x]
    obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G'
      (((1 : G') : G' ⧸ (U : Subgroup G'))) (e x)
    rw [← hs, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient, Subgroup.coe_map]
    let US : Set G' := ((U : Subgroup G') : Set G')
    change IsOpen ((fun z : G' => s * z * s⁻¹) '' US)
    simpa only [Set.image_image] using
      isOpenMap_mul_right s⁻¹ ((fun z : G' => s * z) '' US)
        (isOpenMap_mul_left s US (show IsOpen US from U.isOpen'))
  let X : ContAction FintypeCat.{w} G' :=
    ⟨Action.FintypeCat.ofMulAction G' (FintypeCat.of A), hAcont⟩
  let x₀ : A :=
    e.symm (((1 : G') : G' ⧸ (U : Subgroup G')))
  have hx₀ : ∀ b : G'', h b • x₀ = x₀ := by
    intro b
    apply e.injective
    simp only [Equiv.smul_def, e.apply_symm_apply, x₀]
    rw [← MulAction.mem_stabilizer_iff,
      MulAction.stabilizer_quotient]
    apply hKU
    exact ⟨b, rfl⟩
  have htrans : MulAction.IsPretransitive G' A := by
    constructor
    intro x y
    obtain ⟨s, hs⟩ :=
      MulAction.exists_smul_eq G' (e x) (e y)
    refine ⟨s, e.injective ?_⟩
    simpa only [Equiv.smul_def, e.apply_symm_apply] using hs
  have hall :
      ∀ (b : G'') (x : A), h b • x = x :=
    hfixed X htrans ⟨x₀, hx₀⟩
  let y : A :=
    e.symm (((g⁻¹ : G') : G' ⧸ (U : Subgroup G')))
  have hy := hall a y
  have hyq :
      h a • (((g⁻¹ : G') : G' ⧸ (U : Subgroup G'))) =
        ((g⁻¹ : G') : G' ⧸ (U : Subgroup G')) := by
    have heq := congrArg e hy
    simpa only [Equiv.smul_def, e.apply_symm_apply, y] using heq
  have hconjFix :
      (g * h a * g⁻¹) •
          (((1 : G') : G' ⧸ (U : Subgroup G'))) =
        ((1 : G') : G' ⧸ (U : Subgroup G')) := by
    have heq := congrArg (g • ·) hyq
    simpa only [MulAction.Quotient.smul_coe, smul_eq_mul,
      mul_assoc, mul_inv_cancel, mul_one]
      using heq
  have hconjMem : g * h a * g⁻¹ ∈ (U : Subgroup G') := by
    rw [← MulAction.stabilizer_quotient (U : Subgroup G'),
      MulAction.mem_stabilizer_iff]
    exact hconjFix
  exact hconjU hconjMem

/--
The range of a continuous homomorphism of profinite groups is normal exactly
when one range-fixed point in every transitive finite continuous target
action forces the range to fix the whole action.
-/
theorem range_normal_iff_fixed_point_implies_trivial
    (h : G'' →ₜ* G') :
    h.toMonoidHom.range.Normal ↔
      ∀ X : ContAction FintypeCat.{w} G',
        MulAction.IsPretransitive G' X.obj.V →
        (∃ x : X.obj.V, ∀ a : G'', h a • x = x) →
        ∀ (a : G'') (x : X.obj.V), h a • x = x :=
  ⟨fixed_point_implies_trivial_of_range_normal h,
    range_normal_of_fixed_point_implies_trivial h⟩

end CategoryTheory.ContAction

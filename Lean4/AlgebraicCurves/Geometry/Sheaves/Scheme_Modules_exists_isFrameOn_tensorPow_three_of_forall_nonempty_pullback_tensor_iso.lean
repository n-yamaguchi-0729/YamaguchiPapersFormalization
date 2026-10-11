/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.ProjectivePresentation
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensorPow
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
import AlgebraicCurves.Geometry.Schemes.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import AlgebraicCurves.Geometry.Schemes.jacobsonSpace_of_locallyOfFiniteType
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal

/-!
# Scheme Modules exists is Frame On tensor Pow three of forall nonempty pullback tensor iso
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section l3_solution
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open scoped CategoryTheory.MonObj

namespace L3Sol

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk
  t)]

/-- The rational points of `X` over `Spec k`, expressed as morphisms in the over category. -/
abbrev Pt := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

/-- Right translation by a point of the group object, viewed as a scheme morphism. -/
noncomputable abbrev T (x : Pt t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left

/-- Left translation by a point of the group object, viewed as a scheme morphism. -/
noncomputable abbrev T' (z : Pt t) : X ⟶ X :=
  ((CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z) * 𝟙 (Over.mk t)).left

/-- The inversion morphism of the group object, viewed as a scheme morphism. -/
noncomputable abbrev invT : X ⟶ X := ((𝟙 (Over.mk t))⁻¹ : Over.mk t ⟶ Over.mk t).left
omit [GrpObj (Over.mk t)] in
theorem toUnit_comp_pt (x : Pt t) :
    CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ x = x := by
  have : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [this]
  exact Category.id_comp x

theorem comp_T (z x : Pt t) :
    z ≫ (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)) = z * x := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
    toUnit_comp_pt]

theorem comp_T' (z x : Pt t) :
    x ≫ ((CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z) * 𝟙 (Over.mk t)) = z * x := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
    toUnit_comp_pt]

theorem pt_mul (z x : Pt t) :
    (z * x).left.base (IsLocalRing.closedPoint k) = (T t x).base (z.left.base
      (IsLocalRing.closedPoint k)) := by
  rw [← comp_T t z x, Over.comp_left]
  rfl

theorem pt_mul' (z x : Pt t) :
    (z * x).left.base (IsLocalRing.closedPoint k) = (T' t z).base (x.left.base
      (IsLocalRing.closedPoint k)) := by
  rw [← comp_T' t z x, Over.comp_left]
  rfl

theorem pt_inv (x : Pt t) :
    (x⁻¹).left.base (IsLocalRing.closedPoint k) = (invT t).base (x.left.base
      (IsLocalRing.closedPoint k)) := by
  have h : x ≫ (𝟙 (Over.mk t))⁻¹ = x⁻¹ := by rw [GrpObj.comp_inv, Category.comp_id]
  rw [← h, Over.comp_left]
  rfl

theorem T_inv_comp (x : Pt t) :
    (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)) = 𝟙 (Over.mk t) := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
    mul_assoc, GrpObj.comp_inv, inv_mul_cancel, mul_one]

theorem T'_inv_comp (z : Pt t) :
    ((CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z⁻¹) * 𝟙 (Over.mk t)) ≫
      ((CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z) * 𝟙 (Over.mk t)) = 𝟙 (Over.mk t) := by
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
    ← mul_assoc, GrpObj.comp_inv, mul_inv_cancel, one_mul]

theorem surjective_T (x : Pt t) : Function.Surjective (T t x).base := by
  intro y
  refine ⟨(T t x⁻¹).base y, ?_⟩
  exact congrArg (fun f : Over.mk t ⟶ Over.mk t => f.left.base y) (T_inv_comp t x)

theorem surjective_T' (z : Pt t) : Function.Surjective (T' t z).base := by
  intro y
  refine ⟨(T' t z⁻¹).base y, ?_⟩
  exact congrArg (fun f : Over.mk t ⟶ Over.mk t => f.left.base y) (T'_inv_comp t z)

theorem surjective_invT : Function.Surjective (invT t).base := by
  intro y
  refine ⟨(invT t).base y, ?_⟩
  have h : ((𝟙 (Over.mk t))⁻¹ : Over.mk t ⟶ Over.mk t) ≫ (𝟙 (Over.mk t))⁻¹ = 𝟙 _ := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  exact congrArg (fun f : Over.mk t ⟶ Over.mk t => f.left.base y) h

theorem preimage_ne_univ {α β : Type*} {f : α → β} (hf : Function.Surjective f) {D : Set β}
    (hD : D ≠ Set.univ) : f ⁻¹' D ≠ Set.univ := by
  intro h
  apply hD
  rw [Set.eq_univ_iff_forall] at h ⊢
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact h x

theorem exists_isClosed_singleton_mem_of_isOpen [JacobsonSpace X] {O : Set X} (hO : IsOpen O)
    (hne : O.Nonempty) : ∃ x ∈ O, IsClosed ({x} : Set X) := by
  by_contra h
  push Not at h
  have hsub : closedPoints X ⊆ Oᶜ := fun x hx hxO => h x hxO hx
  have := JacobsonSpace.closure_inter_closedPoints (X := X) isClosed_univ
  rw [Set.univ_inter] at this
  have h2 : closure (closedPoints X) ⊆ Oᶜ := closure_minimal hsub hO.isClosed_compl
  rw [this] at h2
  obtain ⟨x, hx⟩ := hne
  exact h2 (Set.mem_univ x) hx

end L3Sol

end l3_solution
end Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso in
open L3Sol in
theorem Scheme.Modules.exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
          x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
          y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
          (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L) (hθ : θ ≠ 0) :
    ∃ (N : ℕ) (σ : Fin (N + 1) → Γ(L.tensorPow 3, ⊤)) (U : Fin (N + 1) → X.Opens),
      iSup U = ⊤ ∧ ∀ i, Scheme.Modules.IsFrameOn (σ i) (U i) := by
  classical
  have : JacobsonSpace X := jacobsonSpace_of_locallyOfFiniteType t
  let D : Set X := ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X)
  have hDc : IsClosed D := (Scheme.Modules.zeroSchemeIdeal θ).support.isClosed
  have hD : D ≠ Set.univ := fun h =>
    hL.genericPoint_notMem_support_zeroSchemeIdeal θ hθ (by
      have hm := Set.mem_univ (genericPoint X)
      rw [← h] at hm
      exact hm)
  have hL3 : Scheme.Modules.IsInvertible (L.tensorPow 3) := hL.tensorPow 3
  have key : ∀ u : X, IsClosed ({u} : Set X) →
      ∃ s : 𝟙_ X.Modules ⟶ L.tensorPow 3, u ∉ ((Scheme.Modules.zeroSchemeIdeal s).support : Set X)
        := by
    intro u hu
    obtain ⟨u₀, hu₀⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t u hu
    have hA : IsClosed ((T' t u₀).base ⁻¹' D) := hDc.preimage (T' t u₀).base.hom.continuous
    have hAne : ((T' t u₀).base ⁻¹' D)ᶜ.Nonempty :=
      Set.nonempty_compl.2 (preimage_ne_univ (surjective_T' t u₀) hD)
    obtain ⟨pa, hpa, hpac⟩ := exists_isClosed_singleton_mem_of_isOpen hA.isOpen_compl hAne
    obtain ⟨a, ha⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t pa hpac
    let g : X ⟶ X := invT t ≫ T' t u₀ ≫ T t a⁻¹
    have hg : Function.Surjective g.base := by
      change Function.Surjective ((invT t ≫ T' t u₀ ≫ T t a⁻¹).base)
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
      exact ((surjective_T t a⁻¹).comp (surjective_T' t u₀)).comp (surjective_invT t)
    have hB : IsClosed (g.base ⁻¹' D) := hDc.preimage g.base.hom.continuous
    have hO : (((T' t u₀).base ⁻¹' D)ᶜ ∩ (g.base ⁻¹' D)ᶜ).Nonempty := by
      have := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible _ _ hA.isOpen_compl
        hB.isOpen_compl
        (by simpa using hAne) (by simpa using Set.nonempty_compl.2 (preimage_ne_univ hg hD))
      simpa using this
    obtain ⟨pb, ⟨hpb1, hpb2⟩, hpbc⟩ := exists_isClosed_singleton_mem_of_isOpen
      (hA.isOpen_compl.inter hB.isOpen_compl) hO
    obtain ⟨b, hb⟩ := exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t pb hpbc
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq k t L hL
      hsq θ a b
    refine ⟨s, ?_⟩
    rw [hs]
    rintro ((h1 | h2) | h3)
    · apply hpa
      change (T t a).base u ∈ D at h1
      rw [← hu₀, ← pt_mul, pt_mul', ha] at h1
      exact h1
    · apply hpb1
      change (T t b).base u ∈ D at h2
      rw [← hu₀, ← pt_mul, pt_mul', hb] at h2
      exact h2
    · apply hpb2
      change (T t (a * b)⁻¹).base u ∈ D at h3
      rw [← hu₀, ← pt_mul, mul_inv_rev, ← mul_assoc, pt_mul, pt_mul', pt_inv, hb] at h3
      change (g.base) pb ∈ D
      simpa [g, Scheme.Hom.comp_base] using h3
  choose sOf hsOf using key
  let CP := {u : X // IsClosed ({u} : Set X)}
  let W : CP → X.Opens := fun u =>
    ⟨((Scheme.Modules.zeroSchemeIdeal (sOf u.1 u.2)).support : Set X)ᶜ,
      (Scheme.Modules.zeroSchemeIdeal (sOf u.1 u.2)).support.isClosed.isOpen_compl⟩
  have hcov : (⋃ u : CP, (W u : Set X)) = Set.univ := by
    by_contra hne
    have hC : IsClosed (⋃ u : CP, (W u : Set X))ᶜ := (isOpen_iUnion fun u => (W
      u).isOpen).isClosed_compl
    obtain ⟨x, hx, hxc⟩ : ∃ x ∈ (⋃ u : CP, (W u : Set X))ᶜ, IsClosed ({x} : Set X) := by
      have hne' : ((⋃ u : CP, (W u : Set X))ᶜ).Nonempty := Set.nonempty_compl.2 hne
      have := JacobsonSpace.closure_inter_closedPoints (X := X) hC
      by_contra h
      push Not at h
      have hempty : (⋃ u : CP, (W u : Set X))ᶜ ∩ closedPoints X = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun y hy => h y hy.1 hy.2
      rw [hempty, closure_empty] at this
      exact hne'.ne_empty this.symm
    exact hx (Set.mem_iUnion.2 ⟨⟨x, hxc⟩, hsOf x hxc⟩)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace t
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun u : CP => (W u : Set X)) (fun u => (W
    u).isOpen)
    hcov.symm.le
  have hFne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have hx := hF (Set.mem_univ (genericPoint X))
    simp at hx
  obtain ⟨N, hN⟩ : ∃ N, F.card = N + 1 := ⟨F.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2
    hFne)).symm⟩
  let enum : Fin (N + 1) ≃ F := (F.equivFinOfCardEq hN).symm
  refine ⟨N, fun i => (sOf (enum i).1.1 (enum i).1.2).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1),
    fun i => W (enum i).1, ?_, fun i => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have hx := hF (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    exact Opens.mem_iSup.2 ⟨enum.symm ⟨u, hu⟩, by simpa using hxu⟩
  · exact hL3.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal _ _ disjoint_compl_left

end AlgebraicGeometry
end ProofImplementation

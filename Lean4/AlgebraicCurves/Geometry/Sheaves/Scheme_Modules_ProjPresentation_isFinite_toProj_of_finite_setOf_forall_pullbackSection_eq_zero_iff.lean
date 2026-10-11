/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections
import SchemeTheory.Modules.ProjectivePresentation
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensorPow
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint
import AlgebraicCurves.Geometry.Schemes.Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import AlgebraicCurves.Geometry.Schemes.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq

/-!
# Scheme Modules Proj Presentation is Finite to Proj of finite set Of forall pullback
Section eq zero iff
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.FiniteProjectivePresentation
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FiniteStabiliserSketch

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))

/-- The rational points of `X` over `Spec k`, expressed as morphisms in the over category. -/
abbrev Pt := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

/-- The underlying translation morphism determined by the rational point `a`. -/
noncomputable abbrev T [GrpObj (Over.mk t)] (a : Pt t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left

/-- The underlying scheme point of a rational point. -/
noncomputable abbrev pt (z : Pt t) : X := z.left.base (IsLocalRing.closedPoint k)

theorem eq_singleton_of_finite_inter_closedPoints {Y : Type*} [TopologicalSpace Y] [JacobsonSpace Y]
    {Z : Set Y} (hZc : IsClosed Z) (hZi : IsIrreducible Z) (hfin : (Z ∩ closedPoints Y).Finite)
    {x : Y} (hxZ : x ∈ Z) (hxc : IsClosed ({x} : Set Y)) : Z = {x} := by
  have hdisc : IsDiscrete (Z ∩ closedPoints Y) :=
    hfin.isDiscrete_of_subset_closedPoints Set.inter_subset_right
  have hirr : IsIrreducible (Z ∩ closedPoints Y) := by
    rwa [← isIrreducible_iff_closure,
      JacobsonSpace.closure_inter_closedPoints_eq_closure hZc.isLocallyClosed,
        isIrreducible_iff_closure]
  have hsubs : (Z ∩ closedPoints Y).Subsingleton := hdisc.subsingleton_of_isPreirreducible
    hirr.isPreirreducible
  have h1 : Z ∩ closedPoints Y = {x} := hsubs.eq_singleton_of_mem ⟨hxZ, hxc⟩
  calc Z = closure Z := hZc.closure_eq.symm
    _ = closure (Z ∩ closedPoints Y) :=
        (JacobsonSpace.closure_inter_closedPoints_eq_closure hZc.isLocallyClosed).symm
    _ = {x} := by rw [h1, hxc.closure_eq]

end FiniteStabiliserSketch
end AlgebraicCurves.Geometry.Sheaves.Proofs.FiniteProjectivePresentation

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.FiniteProjectivePresentation
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
attribute [local instance] MvPolynomial.gradedAlgebra


open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.FiniteProjectivePresentation in
open FiniteStabiliserSketch in
theorem isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
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
    (θ : 𝟙_ X.Modules ⟶ L)
    (hK : Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left
            θ = 0})
    {N : ℕ} (𝔓 : (L.tensorPow 3).ProjPresentation t N) :
    IsFinite 𝔓.toProj := by
  have : IsProper (𝔓.toProj ≫ ProjSpace.π k N) := by rw [𝔓.toProj_π]; infer_instance
  have : IsProper 𝔓.toProj := IsProper.of_comp 𝔓.toProj (ProjSpace.π k N)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t
  by_contra hfin
  have hnlqf : ¬ LocallyQuasiFinite 𝔓.toProj := fun h => hfin
    (IsFinite.of_isProper_of_locallyQuasiFinite _)
  obtain ⟨x, hxc, hx⟩ : ∃ x : X, IsClosed ({x} : Set X) ∧ ¬ 𝔓.toProj.QuasiFiniteAt x := by
    have hne : ((𝔓.toProj.quasiFiniteLocus : Set X)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      intro htop
      apply hnlqf
      rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
      exact TopologicalSpace.Opens.ext (htop.trans TopologicalSpace.Opens.coe_top.symm)
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace t
    obtain ⟨x, hx, hxc⟩ := IsClosed.exists_closed_singleton
      (𝔓.toProj.quasiFiniteLocus.isOpen.isClosed_compl) hne
    exact ⟨x, hxc, fun h => hx (Scheme.Hom.mem_quasiFiniteLocus.mpr h)⟩
  obtain ⟨Z, hZc, hZi, hxZ, hZne, hZfib⟩ :=
    Scheme.Hom.exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt 𝔓.toProj x hx
  have hyc : IsClosed ({𝔓.toProj.base x} : Set _) := by
    have := (𝔓.toProj.isClosedMap) _ hxc
    rwa [Set.image_singleton] at this
  have hZy : Z ⊆ 𝔓.toProj.base ⁻¹' {𝔓.toProj.base x} := by rwa [hyc.closure_eq] at hZfib
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t
    x hxc
  set D : Set X := ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) with hD
  have hDc : IsClosed D := (Scheme.Modules.zeroSchemeIdeal θ).support.isClosed
  have hdich : ∀ a b : Pt t,
      Z ⊆ ((T t a).base ⁻¹' D ∪ (T t b).base ⁻¹' D ∪ (T t (a * b)⁻¹).base ⁻¹' D) ∨
        Disjoint Z ((T t a).base ⁻¹' D ∪ (T t b).base ⁻¹' D ∪ (T t (a * b)⁻¹).base ⁻¹' D) := by
    intro a b
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq k t L hL
      hsq θ a b
    have h3 := Scheme.Modules.ProjPresentation.subset_support_zeroSchemeIdeal_or_disjoint k t
      (L.tensorPow 3)
      (hL.tensorPow 3) 𝔓 Z hZc hZi (𝔓.toProj.base x) hyc hZy s
    rw [hs] at h3
    exact h3
  have hvan : ∀ w : Pt t, Scheme.Modules.pullbackSection w.left θ = 0 ↔ pt t w ∈ D := fun w =>
    hL.pullbackSection_eq_zero_iff_mem_support θ w.left
  have hstab : ∀ z' : Pt t, pt t z' ∈ Z → ∀ w : Pt t, pt t w ∈ D ↔ pt t (w * (z⁻¹ * z')) ∈ D := by
    intro z' hz' w
    by_cases hDu : D = Set.univ
    · simp [hDu]
    exact Scheme.forall_mem_iff_of_subset_union_preimage_or_disjoint k t D hDc hDu Z hZc hZi hdich
      z z'
      (hz ▸ hxZ) hz' w
  have hsub : Z ∩ closedPoints X ⊆
      (fun κ : Pt t => pt t (z * κ)) ''
        {x : Pt t | ∀ w : Pt t,
          Scheme.Modules.pullbackSection w.left θ = 0 ↔ Scheme.Modules.pullbackSection (w * x).left
            θ = 0} := by
    rintro x' ⟨hx'Z, hx'c⟩
    obtain ⟨z', hz'⟩ :=
      AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t x' hx'c
    have hz'Z : pt t z' ∈ Z := by rw [show pt t z' = x' from hz']; exact hx'Z
    refine ⟨z⁻¹ * z', fun w => (hvan w).trans ((hstab z' hz'Z w).trans (hvan _).symm), ?_⟩
    change pt t (z * (z⁻¹ * z')) = x'
    rw [mul_inv_cancel_left]
    exact hz'
  have hZfin : (Z ∩ closedPoints X).Finite := (hK.image _).subset hsub
  exact hZne (eq_singleton_of_finite_inter_closedPoints hZc hZi hZfin hxZ hxc)
end AlgebraicGeometry.Scheme.Modules.ProjPresentation
end ProofImplementation

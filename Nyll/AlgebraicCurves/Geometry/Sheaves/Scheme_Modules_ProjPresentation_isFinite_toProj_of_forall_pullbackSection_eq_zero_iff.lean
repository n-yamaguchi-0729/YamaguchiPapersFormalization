/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensorPow
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_ProjPresentation_subset_support_zeroSchemeIdeal_or_disjoint
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_forall_mem_iff_of_subset_union_preimage_or_disjoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_mem_isClosed_singleton_ne_of_isIrreducible
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
import Nyll.SchemeTheory.Modules.TensorSections

/-!
# Scheme Modules Proj Presentation is Finite to Proj of forall pullback Section eq zero iff
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
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

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

namespace L2Sketch

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))

/-- The rational points of `X` over `Spec k`, expressed as morphisms in the over category. -/
abbrev Pt := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

/-- The underlying translation morphism determined by the rational point `a`. -/
noncomputable abbrev T [GrpObj (Over.mk t)] (a : Pt t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left

/-- The underlying scheme point of a rational point. -/
noncomputable abbrev pt (z : Pt t) : X := z.left.base (IsLocalRing.closedPoint k)

end L2Sketch

end Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff in
open L2Sketch in
theorem isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
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
    (hK : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      (∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ
          = 0) →
      x = 1)
    {N : ℕ} (𝔓 : (L.tensorPow 3).ProjPresentation t N) :
    IsFinite 𝔓.toProj := by
  have : IsProper (𝔓.toProj ≫ ProjSpace.π k N) := by rw [𝔓.toProj_π]; infer_instance
  have : IsProper 𝔓.toProj := IsProper.of_comp 𝔓.toProj (ProjSpace.π k N)
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
  obtain ⟨x', hx'Z, hx'c, hx'x⟩ :=
    AlgebraicGeometry.exists_mem_isClosed_singleton_ne_of_isIrreducible k t Z hZc hZi x hxZ hxc hZne
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k t
    x hxc
  obtain ⟨z', hz'⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k
    t x' hx'c
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
  have hstab : ∀ w : Pt t, pt t w ∈ D ↔ pt t (w * (z⁻¹ * z')) ∈ D := by
    intro w
    by_cases hDu : D = Set.univ
    · simp [hDu]
    by_cases hDe : D = ∅
    · simp [hDe]
    exact Scheme.forall_mem_iff_of_subset_union_preimage_or_disjoint k t D hDc hDu Z hZc hZi hdich
      z z'
      (hz ▸ hxZ) (hz' ▸ hx'Z) w
  have key : z⁻¹ * z' = 1 := hK _ (fun w => (hvan w).trans ((hstab w).trans (hvan _).symm))
  have hzz : z' = z := by
    have := congrArg (fun u => z * u) key
    simpa [← mul_assoc] using this
  exact hx'x (hz' ▸ hz ▸ congrArg (fun u : Pt t => pt t u) hzz)

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
end ProofImplementation

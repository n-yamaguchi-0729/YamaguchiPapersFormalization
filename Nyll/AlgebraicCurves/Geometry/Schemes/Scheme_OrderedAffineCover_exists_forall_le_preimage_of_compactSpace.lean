/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech

/-!
# Scheme Ordered Affine Cover exists forall le preimage of compact Space
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.exists_forall_le_preimage_of_compactSpace
    {Y : Scheme.{u}} [CompactSpace Y] {n : ℕ} (X : Fin n → Scheme.{u}) (h : ∀ j, Y ⟶ X j)
    (𝒰 : ∀ j, (X j).OrderedAffineCover) :
    ∃ (𝒲 : Y.OrderedAffineCover) (lam : ∀ j, 𝒲.ι → (𝒰 j).ι),
      ∀ (j : Fin n) (w : 𝒲.ι), 𝒲.U w ≤ (h j) ⁻¹ᵁ (𝒰 j).U (lam j w) := by
  classical
  have hidx : ∀ (y : Y) (j : Fin n), ∃ i : (𝒰 j).ι, (h j).base y ∈ (𝒰 j).U i := by
    intro y j
    have hy : (h j).base y ∈ (⊤ : (X j).Opens) := trivial
    rw [← (𝒰 j).iSup_eq_top] at hy
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  choose a ha using hidx
  have hW : ∀ y : Y, ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧
      ∀ j : Fin n, (W : Set Y) ⊆ (h j).base ⁻¹' ((𝒰 j).U (a y j) : Set (X j)) := by
    intro y
    set O : Set Y := ⋂ j : Fin n, (h j).base ⁻¹' ((𝒰 j).U (a y j) : Set (X j)) with hO
    have hOopen : IsOpen O :=
      isOpen_iInter_of_finite fun j => ((𝒰 j).U (a y j)).isOpen.preimage (h j).base.hom.continuous
    have hyO : y ∈ O := Set.mem_iInter.mpr fun j => ha y j
    obtain ⟨_, ⟨W, hWaff, rfl⟩, hyW, hWO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyO
      hOopen
    exact ⟨W, hWaff, hyW, fun j => hWO.trans (Set.iInter_subset _ j)⟩
  choose W hWaff hyW hWsub using hW
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyW y⟩)
  let : LinearOrder (↥t) := LinearOrder.lift' (Fintype.equivFin (↥t)) (Fintype.equivFin
    (↥t)).injective
  refine ⟨{ ι := ↥t
            U := fun w => W w.1
            isAffineOpen := fun w => hWaff w.1
            iSup_eq_top := ?_ }, fun j w => a w.1 j, fun j w => ?_⟩
  · refine top_le_iff.mp fun y _ => ?_
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨w, hw⟩, hyw⟩
  · intro y hy
    exact hWsub w.1 j hy
end Scheme_OrderedAffineCover_exists_forall_le_preimage_of_compactSpace
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

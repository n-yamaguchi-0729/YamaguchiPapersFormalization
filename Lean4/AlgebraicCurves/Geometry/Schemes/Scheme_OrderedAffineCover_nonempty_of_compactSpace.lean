/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech

/-!
# Scheme Ordered Affine Cover nonempty of compact Space
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_OrderedAffineCover_nonempty_of_compactSpace

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCover.nonempty_of_compactSpace (V :
  Scheme.{u}) [CompactSpace V] : Nonempty V.OrderedAffineCover := by
  have hcov_all : (Set.univ : Set V) ⊆ ⋃ W : V.affineOpens, (W.1 : Set V) := fun x _ => by
    obtain ⟨W, hWaff, hxW, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.isBasis_affineOpens
        (show x ∈ (⊤ : V.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨⟨W, hWaff⟩, hxW⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun W : V.affineOpens => (W.1 : Set V))
    (fun W => W.1.2) hcov_all
  let _lo : LinearOrder V.affineOpens := IsWellOrder.linearOrder WellOrderingRel
  refine ⟨{ ι := S, U := fun i => i.1.1, isAffineOpen := fun i => i.1.2, iSup_eq_top := ?_ }⟩
  refine le_antisymm le_top (fun x _ => ?_)
  rcases Set.mem_iUnion₂.mp (hS (Set.mem_univ x)) with ⟨W, hWS, hxW⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWS⟩, hxW⟩
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_OrderedAffineCover_nonempty_of_compactSpace
end ProofImplementation

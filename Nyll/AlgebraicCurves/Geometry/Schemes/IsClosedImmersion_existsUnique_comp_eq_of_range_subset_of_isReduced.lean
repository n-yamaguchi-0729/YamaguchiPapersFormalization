/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

/-!
# Is Closed Immersion exists Unique comp eq of range subset of is Reduced
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    {X Y T : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : T ⟶ X) [IsReduced T]
    (H : Set.range f.base ⊆ Set.range i.base) :
    ∃! g : T ⟶ Y, g ≫ i = f := by
  have hZ : IsClosed (Set.range i.base) := i.isClosedEmbedding.isClosed_range
  have hle : i.ker ≤ f.ker := by
    obtain ⟨-, h2⟩ :=
      AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (⟨Set.range i.base, hZ⟩ : Closeds X)
    refine le_trans ?_ (h2 f H)
    have hsupp : i.ker.support = ⟨Set.range i.base, hZ⟩ := by
      ext1
      rw [Scheme.Hom.support_ker]
      exact hZ.closure_eq
    rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_radical _
  refine ⟨IsClosedImmersion.lift i f hle, IsClosedImmersion.lift_fac i f hle, fun g hg => ?_⟩
  rw [← cancel_mono i, hg, IsClosedImmersion.lift_fac]
end IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

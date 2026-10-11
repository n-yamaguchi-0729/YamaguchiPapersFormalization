/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Fiber
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_le_topologicalKrullDim
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_topologicalKrullDim_le

/-!
# Smooth Of Relative Dimension topological Krull Dim preimage singleton eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f]
    (y : ↥Y) (hy : (f.base ⁻¹' {y}).Nonempty) :
    topologicalKrullDim ↥(f.base ⁻¹' {y}) = n := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => SmoothOfRelativeDimension n h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  have : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
    hbc.of_isPullback (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))
      ‹SmoothOfRelativeDimension n f›
  have hne : Nonempty ↥(f.fiber y) := by
    obtain ⟨x, hx⟩ := hy
    exact ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩
  have h1 : (n : WithBot ℕ∞) ≤ topologicalKrullDim ↥(f.fiber y) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h2 : topologicalKrullDim ↥(f.fiber y) ≤ n :=
    AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
      (K := ↑(Y.residueField y)) (f.fiberToSpecResidueField y) n
  have h3 : topologicalKrullDim ↥(f.fiber y) = topologicalKrullDim ↥(f.base ⁻¹' {y}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo y).isHomeomorph
  rw [← h3]
  exact le_antisymm h2 h1
end SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

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

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed

/-!
# Discrete valuation stalks along a section

A section of an integral smooth curve over a field determines a closed point whose stalk
is a discrete valuation ring.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem _root_.AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsDiscreteValuationRing (X.presheaf.stalk (p.base (IsLocalRing.closedPoint k))) := by
  apply AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id _ _ hp
  have h := p.isClosedEmbedding.isClosed_range
  have hr : Set.range p.base = {p.base (IsLocalRing.closedPoint k)} :=
    Set.range_eq_singleton_iff.mpr fun y => congrArg p.base (Subsingleton.elim _ _)
  rwa [hr] at h
end SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

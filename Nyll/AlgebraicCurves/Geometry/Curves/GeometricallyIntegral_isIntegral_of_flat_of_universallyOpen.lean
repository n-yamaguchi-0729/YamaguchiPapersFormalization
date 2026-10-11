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

import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Integrality over an integral base

A flat, universally open, geometrically integral morphism has an integral total scheme
when its base is integral.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem finite_irreducibleComponents_of_irreducibleSpace (S : Type*) [TopologicalSpace S]
    [IrreducibleSpace S] : (irreducibleComponents S).Finite := by
  refine (Set.finite_singleton (Set.univ : Set S)).subset ?_
  intro Z hZ
  rw [Set.mem_singleton_iff]
  exact hZ.eq_of_le (IrreducibleSpace.isIrreducible_univ S) (Set.subset_univ Z)

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] : IsIntegral X := by
  have : Finite (irreducibleComponents S) :=
    (AlgebraicGeometry.finite_irreducibleComponents_of_irreducibleSpace S).to_subtype
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩
end GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation

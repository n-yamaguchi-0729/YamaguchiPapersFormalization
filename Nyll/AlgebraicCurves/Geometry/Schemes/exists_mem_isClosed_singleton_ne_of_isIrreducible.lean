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

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Closure
import Mathlib.Topology.Irreducible
import Mathlib.Tactic.Push

/-!
# exists mem is Closed singleton ne of is Irreducible
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.exists_mem_isClosed_singleton_ne_of_isIrreducible

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_mem_isClosed_singleton_ne_of_isIrreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType
      t]
    (Z : Set X) (hZ : IsClosed Z) (_hZ' : IsIrreducible Z)
    (x : X) (hxZ : x ∈ Z) (hx : IsClosed ({x} : Set X)) (hne : Z ≠ {x}) :
    ∃ x' ∈ Z, IsClosed ({x'} : Set X) ∧ x' ≠ x := by
  let _ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t
  by_contra h
  push Not at h
  apply hne
  have hsub : Z ∩ closedPoints X ⊆ {x} := by
    rintro y ⟨hyZ, hy⟩
    exact h y hyZ (mem_closedPoints_iff.mp hy)
  have h1 : Z ⊆ {x} := by
    rw [← JacobsonSpace.closure_inter_closedPoints hZ]
    exact (closure_mono hsub).trans hx.closure_subset
  exact Set.Subset.antisymm h1 (Set.singleton_subset_iff.mpr hxZ)
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_mem_isClosed_singleton_ne_of_isIrreducible
end ProofImplementation

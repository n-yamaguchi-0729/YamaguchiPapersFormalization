/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.KrullDimension

/-!
# Is Irreducible topological Krull Dim add one le of is Closed of ne
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne

open Set Order TopologicalSpace Topology

universe u

namespace P2mDim

variable {X : Type u} [TopologicalSpace X] {Y Z : Set X}

/-- The whole irreducible subspace as an irreducible closed subset of itself. -/
def topIC (hZ : IsIrreducible Z) : IrreducibleCloseds Z where
  carrier := univ
  isIrreducible' := by
    have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ
    exact IrreducibleSpace.isIrreducible_univ Z
  isClosed' := isClosed_univ

/-- The map on irreducible closed subsets induced by inclusion of the underlying subspaces. -/
def push (hYZ : Y ⊆ Z) : IrreducibleCloseds Y → IrreducibleCloseds Z :=
  IrreducibleCloseds.map (inclusion hYZ) (continuous_inclusion hYZ)

theorem push_strictMono (hYZ : Y ⊆ Z) : StrictMono (push (X := X) hYZ) :=
  IrreducibleCloseds.map_strictMono_of_isInducing (IsEmbedding.inclusion hYZ).isInducing

theorem coe_push_subset (hYZ : Y ⊆ Z) (hY : IsClosed Y) (s : IrreducibleCloseds Y) :
    ((push hYZ s : IrreducibleCloseds Z) : Set Z) ⊆ (Subtype.val ⁻¹' Y : Set Z) := by
  change closure (inclusion hYZ '' (s : Set Y)) ⊆ _
  refine closure_minimal ?_ (hY.preimage continuous_subtype_val)
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem push_lt_top (hZ : IsIrreducible Z) (hYZ : Y ⊆ Z) (hY : IsClosed Y) (hne : Y ≠ Z)
    (s : IrreducibleCloseds Y) : push hYZ s < topIC hZ := by
  refine lt_of_le_of_ne (fun _ _ => trivial) fun h => hne ?_
  refine subset_antisymm hYZ fun z hz => ?_
  have hmem : (⟨z, hz⟩ : Z) ∈ ((push hYZ s : IrreducibleCloseds Z) : Set Z) := by
    rw [h]; trivial
  exact coe_push_subset hYZ hY s hmem

theorem main (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z := by
  unfold topologicalKrullDim
  cases isEmpty_or_nonempty (IrreducibleCloseds Y) with
  | inl h =>
    rw [krullDim_eq_bot]
    exact bot_le
  | inr h =>
    rw [← krullDim_WithTop]
    let g : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds Z :=
      fun a => WithTop.recTopCoe (topIC hZ) (fun s => push hYZ s) a
    refine krullDim_le_of_strictMono g fun a b hab => ?_
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe s =>
      induction b using WithTop.recTopCoe with
      | top => exact push_lt_top hZ hYZ hY hne s
      | coe t => exact push_strictMono hYZ (WithTop.coe_lt_coe.mp hab)

end P2mDim

theorem _root_.IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
    {X : Type u} [TopologicalSpace X] {Y Z : Set X}
    (hZ : IsIrreducible Z) (hY : IsClosed Y) (hYZ : Y ⊆ Z) (hne : Y ≠ Z) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim Z :=
  P2mDim.main hZ hY hYZ hne
end IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

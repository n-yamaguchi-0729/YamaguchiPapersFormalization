/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Defs

/-!
# Valued v tprod eq finset Prod of forall not mem v eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs.Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one

open scoped Topology
open Filter

theorem _root_.Valued.v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {ι : Type*} (f : ι → K) (hf : Multipliable f)
    (S : Finset ι) (hS : ∀ i, i ∉ S → Valued.v (f i) = 1) :
    Valued.v (∏' i, f i) = ∏ i ∈ S, Valued.v (f i) := by
  classical
  have hprod := hf.hasProd
  have hpart : ∀ T : Finset ι, S ⊆ T → Valued.v (∏ i ∈ T, f i) = Valued.v (∏ i ∈ S, f i) := by
    intro T hT
    rw [map_prod, map_prod, ← Finset.prod_sdiff hT, Finset.prod_eq_one (fun i hi => hS i
      (Finset.mem_sdiff.mp hi).2),
      one_mul]
  have hres : ∀ x y : K, Valued.v x = Valued.v y ↔
      (Valued.v : Valuation K Γ₀).restrict x = (Valued.v : Valuation K Γ₀).restrict y := by
    intro x y
    constructor
    · intro h
      apply le_antisymm
      · rw [← not_lt, Valuation.restrict_lt_iff, not_lt, h]
      · rw [← not_lt, Valuation.restrict_lt_iff, not_lt, h]
    · intro h
      apply le_antisymm
      · rw [← not_lt, ← Valuation.restrict_lt_iff, not_lt, h]
      · rw [← not_lt, ← Valuation.restrict_lt_iff, not_lt, h]
  have hclosed := Valued.isClosed_sphere (R := K) ((Valued.v : Valuation K Γ₀).restrict (∏ i ∈ S, f
    i))
  have hev : ∀ᶠ T : Finset ι in atTop,
      (∏ i ∈ T, f i) ∈ {x : K | (Valued.v : Valuation K Γ₀).restrict x =
        (Valued.v : Valuation K Γ₀).restrict (∏ i ∈ S, f i)} := by
    filter_upwards [eventually_ge_atTop S] with T hT
    exact (hres _ _).mp (hpart T hT)
  have hmem := hclosed.mem_of_tendsto hprod hev
  rw [Set.mem_ofPred_eq] at hmem
  rw [(hres _ _).mpr hmem, map_prod]
end AlgebraicCurves.Valuations.Proofs.Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
end ProofImplementation

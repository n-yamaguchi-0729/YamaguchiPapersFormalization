/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
Adelic families are precisely repartitions, using a divisor bound for their valuations.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Mem_adeleSpace_iff_mem_repartitions

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_repartitionsOf_iff_coe_mem_adeleBdd {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl

theorem mem_repartitions_of_mem_adeleBdd {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd
    D) :
    α ∈ repartitions K F :=
  mem_repartitions_of_forall_le_exp D α hα

theorem mem_repartitions_of_mem_adeleSpace {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    α ∈ repartitions K F := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact mem_repartitions_of_mem_adeleBdd hD

theorem diagonalHom_eq_coe_algebraMap (f : F) :
    diagonalHom K F f = ((algebraMap F ↥(repartitions K F) f : ↥(repartitions K F)) : Place K F →
      F) := rfl

theorem mem_principalRepartitions_iff_coe_mem_globalSub {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔ (α : Place K F → F) ∈ globalSub K F := by
  rw [mem_principalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

/-- Families bounded at every place by the valuation bound of a single divisor. -/
noncomputable def boundedFamilies [HasPrincipalDivisors K F] : Subalgebra F (Place K F → F) where
  carrier := {α | ∃ D : Divisor K F, ∀ v : Place K F, v.adicValuation (α v) ≤ exp (D v)}
  mul_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D + E, fun v => ?_⟩
    rw [Pi.mul_apply, map_mul, Finsupp.add_apply, exp_add]
    exact mul_le_mul' (hD v) (hE v)
  add_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D ⊔ E, fun v => ?_⟩
    rw [Pi.add_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · exact (hD v).trans (exp_le_exp.mpr (le_sup_left (a := D) (b := E) v))
    · exact (hE v).trans (exp_le_exp.mpr (le_sup_right (a := D) (b := E) v))
  algebraMap_mem' := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · exact ⟨0, fun v => by simp⟩
    · obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
      refine ⟨-P, fun v => ?_⟩
      rw [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        v.adicValuation_eq_exp_neg_ord hf, Finsupp.neg_apply, hP]

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.Proofs in
open _root_.AlgebraicCurve Mem_adeleSpace_iff_mem_repartitions.AlgebraicCurve WithZero in
theorem _root_.AlgebraicCurve.mem_adeleSpace_iff_mem_repartitions {K F : Type*} [Field K] [Field
    F] [Algebra K F] [HasPrincipalDivisors K F] {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F := by
  constructor
  · exact mem_repartitions_of_mem_adeleSpace
  · intro hα
    have h : repartitions K F ≤ boundedFamilies (K := K) (F := F) := by
      refine Algebra.adjoin_le ?_
      intro β hβ
      classical
      let S : Finset (Place K F) := hβ.toFinset
      refine ⟨∑ v ∈ S, Finsupp.single v (-(v.ord (β v))), fun v => ?_⟩
      by_cases hv : v ∈ S
      · have hβv : β v ≠ 0 := by
          intro h0
          have : ¬v.adicValuation (β v) ≤ 1 := by simpa [S] using hv
          apply this; simp [h0]
        rw [v.adicValuation_eq_exp_neg_ord hβv, exp_le_exp, Finsupp.finsetSum_apply,
          Finset.sum_eq_single v (fun w _ hw => Finsupp.single_eq_of_ne (Ne.symm hw)) (fun h => (h
            hv).elim),
          Finsupp.single_eq_same]
      · have : v.adicValuation (β v) ≤ 1 := by
          by_contra h; exact hv (by simpa [S] using h)
        refine this.trans ?_
        rw [Finsupp.finsetSum_apply, Finset.sum_eq_zero (fun w hw => ?_), exp_zero]
        exact Finsupp.single_eq_of_ne (fun h => hv (h ▸ hw))
    obtain ⟨D, hD⟩ := h hα
    exact adeleBdd_le_adeleSpace (D := D) hD
end AlgebraicCurves.Cohomology.Proofs.Mem_adeleSpace_iff_mem_repartitions
end ProofImplementation

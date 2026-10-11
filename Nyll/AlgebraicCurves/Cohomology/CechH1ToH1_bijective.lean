/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_cechH1ToH1_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Cohomology.Mem_adeleSpace_iff_mem_repartitions
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt

/-!
Bijectivity of the map from divisor-section Cech cohomology to adelic cohomology.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.CechH1ToH1_bijective

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_setOf_not_adicValuation_le_of_mem_adeleBdd {E : Divisor K F} {β : Place K F → F}
    (hβ : β ∈ adeleBdd E) (D : Divisor K F) :
    {v : Place K F | ¬ v.adicValuation (β v) ≤ WithZero.exp (D v)}.Finite := by
  refine ((E - D).support.finite_toSet).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, not_le] at hv
  have hE := (mem_adeleBdd.mp hβ) v
  have hlt : WithZero.exp (D v) < WithZero.exp (E v) := lt_of_lt_of_le hv hE
  rw [WithZero.exp_lt_exp] at hlt
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.sub_apply]
  omega

theorem finite_setOf_not_adicValuation_le_of_mem_adeleSpace {β : Place K F → F}
    (hβ : β ∈ adeleSpace K F) (D : Divisor K F) :
    {v : Place K F | ¬ v.adicValuation (β v) ≤ WithZero.exp (D v)}.Finite := by
  obtain ⟨E, hE⟩ := mem_adeleSpace_iff.mp hβ
  exact finite_setOf_not_adicValuation_le_of_mem_adeleBdd hE D

end AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

theorem cechH1ToH1_injective {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (D : Divisor K F) :
    Function.Injective (cechH1ToH1 hcover D) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, cechH1ToH1_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_sup] at hx
  obtain ⟨a, ha, p, hp, hap⟩ := hx
  obtain ⟨h, hh⟩ := mem_principalRepartitions_iff.mp hp
  have ha' : ∀ v : Place K F, v.adicValuation ((a : Place K F → F) v) ≤ WithZero.exp (D v) := ha
  rw [Submodule.Quotient.mk_eq_zero, mem_range_cechDiff_iff]
  have key : ∀ v : Place K F,
      (a : Place K F → F) v + h = (extendOffChart K S₀ (f : F) : Place K F → F) v := by
    intro v
    have := congrArg (fun α : ↥(repartitions K F) => (α : Place K F → F) v) hap
    simpa only [AddMemClass.coe_add, Pi.add_apply, hh] using this
  have hhS₀ : h ∈ lSpaceOn S₀ D := by
    intro v hv
    have hv' := key v
    rw [coe_extendOffChart_apply_of_mem _ hv] at hv'
    rw [eq_neg_of_add_eq_zero_right hv', Valuation.map_neg]
    exact ha' v
  have hfh : (f : F) - h ∈ lSpaceOn S₁ D := by
    intro v hv
    by_cases hv₀ : v ∈ S₀
    · exact (Valuation.map_sub _ _ _).trans (max_le (f.2 v ⟨hv₀, hv⟩) (hhS₀ v hv₀))
    · have hv' := key v
      rw [coe_extendOffChart_apply_of_not_mem _ hv₀] at hv'
      rw [show (f : F) - h = (a : Place K F → F) v by rw [← hv']; ring]
      exact ha' v
  rw [show (f : F) = h + ((f : F) - h) by ring]
  exact Submodule.add_mem_sup hhS₀ hfh

end AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

theorem cechH1ToH1_surjective {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    Function.Surjective (cechH1ToH1 hcover D) := by
  classical
  obtain ⟨v₀, hv₀⟩ := h₀
  obtain ⟨v₁, hv₁⟩ := h₁
  intro x
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hαA : (α : Place K F → F) ∈ adeleSpace K F := mem_adeleSpace_iff_mem_repartitions.mpr α.2
  obtain ⟨hf, hhf⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt h S₀ hv₀ D (α :
    Place K F → F)
    ((finite_setOf_not_adicValuation_le_of_mem_adeleSpace hαA D).subset fun v hv => hv.2)
  set α'' : Place K F → F := fun v => if v ∈ S₀ then 0 else (α : Place K F → F) v - hf with hα''
  have hα''fin : {v : Place K F | ¬ v.adicValuation (α'' v) ≤ WithZero.exp (D v)}.Finite := by
    have hA' : (fun v => (α : Place K F → F) v - hf) ∈ adeleSpace K F := by
      have := Submodule.sub_mem _ hαA (diagonal_mem_adeleSpace (K := K) hf)
      convert this using 1
      rfl
    refine (finite_setOf_not_adicValuation_le_of_mem_adeleSpace hA' D).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    by_cases hvS : v ∈ S₀
    · simp only [hα'', ite_eq_left hvS] at hv; exact absurd (by simp) hv
    · simp only [hα'', ite_eq_right hvS] at hv; exact hv
  obtain ⟨g, hg⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt h S₁ hv₁ D α''
    (hα''fin.subset fun v hv => hv.2)
  have hgL : g ∈ lSpaceOn (S₀ ∩ S₁) D := by
    intro v hv
    have := hg v hv.2
    simp only [hα'', ite_eq_left hv.1, zero_sub, Valuation.map_neg] at this
    exact this
  refine ⟨Submodule.Quotient.mk ⟨g, hgL⟩, ?_⟩
  rw [cechH1ToH1_mk, Submodule.Quotient.eq]
  have hbdd : α - algebraMap F (↥(repartitions K F)) hf - extendOffChart K S₀ g ∈ repartitionsOf D
    := by
    intro v
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, Pi.sub_apply, Pi.sub_apply,
      Subalgebra.coe_algebraMap, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    by_cases hvS : v ∈ S₀
    · rw [coe_extendOffChart_apply_of_mem g hvS, sub_zero]
      exact hhf v hvS
    · have hv₁' : v ∈ S₁ := by
        have : v ∈ S₀ ∪ S₁ := hcover ▸ Set.mem_univ v
        exact this.resolve_left hvS
      rw [coe_extendOffChart_apply_of_not_mem g hvS]
      have := hg v hv₁'
      simp only [hα'', ite_eq_right hvS] at this
      exact this
  have hprin := algebraMap_mem_principalRepartitions (K := K) (F := F) hf
  have hmem : α - extendOffChart K S₀ g ∈ repartitionsOf D ⊔ principalRepartitions K F := by
    have heq : α - extendOffChart K S₀ g
        = (α - algebraMap F (↥(repartitions K F)) hf - extendOffChart K S₀ g)
          + algebraMap F (↥(repartitions K F)) hf := by abel
    rw [heq]
    exact Submodule.add_mem_sup hbdd hprin
  have := Submodule.neg_mem _ hmem
  rwa [neg_sub] at this

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.Proofs in
open _root_.AlgebraicCurve CechH1ToH1_bijective.AlgebraicCurve in
theorem _root_.AlgebraicCurve.cechH1ToH1_bijective {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    Function.Bijective (cechH1ToH1 hcover D) :=
  ⟨cechH1ToH1_injective hcover D, cechH1ToH1_surjective h hcover h₀ h₁ D⟩
end AlgebraicCurves.Cohomology.Proofs.CechH1ToH1_bijective
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.JacobianVarieties.Pic0.Pic0_mem_closure_mk_single_sub_single
import Nyll.AlgebraicCurves.Places.Place_exists_forall_ord_eq

/-!
# Generators of the degree-zero Picard group avoiding a finite set

Weak approximation moves a divisor away from any prescribed finite set of places.
The resulting differences with a fixed place generate the degree-zero Picard group.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_mem_closure_mk_single_sub_single_of_notMem

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single_of_notMem
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (S : Finset (Place K F)) (V₀ : Place K F) (hV₀ : V₀ ∉ S) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F) (_ : V ∉ S)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by
  classical
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  set G : Set (Pic0 K F) := {y : Pic0 K F | ∃ (V : Place K F) (_ : V ∉ S)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} with hG
  have hgen_mem : ∀ V : Place K F,
      Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F) := by
    intro V
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
    exact sub_self _
  have hgen : ∀ V : Place K F, V ∉ S →
      Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hgen_mem V⟩ ∈
        AddSubgroup.closure G :=
    fun V hV => AddSubgroup.subset_closure ⟨V, hV, hgen_mem V, rfl⟩
  have key : ∀ (D : Divisor K F) (hD : D ∈ Divisor.degZero (K := K) (F := F)),
      (∀ v ∈ S, D v = 0) → Pic0.mk ⟨D, hD⟩ ∈ AddSubgroup.closure G := by
    intro D hD hS
    have hsum : (∑ v ∈ D.support, D v) = 0 := by
      have h := hD
      rw [Divisor.mem_degZero] at h
      have : Divisor.degree D = ∑ v ∈ D.support, D v := by
        conv_lhs => rw [← Finsupp.sum_single D]
        rw [Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Divisor.degree_single, hdeg1]
        exact mul_one _
      rw [← this, h]
    have h1 : ∑ v ∈ D.support, D v • Finsupp.single v (1 : ℤ) = D := by
      conv_rhs => rw [← Finsupp.sum_single D]
      rw [Finsupp.sum]
      exact Finset.sum_congr rfl fun v _ => Finsupp.smul_single_one v (D v)
    have hDiv : ∑ v ∈ D.support, D v • (Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1) = D := by
      have h2 : ∑ v ∈ D.support, D v • (Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1) =
          ∑ v ∈ D.support, D v • Finsupp.single v (1 : ℤ) -
            (∑ v ∈ D.support, D v) • Finsupp.single V₀ 1 := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun v _ => smul_sub _ _ _
      rw [h2, hsum, zero_smul, sub_zero, h1]
    have hDeq : (⟨D, hD⟩ : Divisor.degZero (K := K) (F := F)) =
        ∑ v ∈ D.support, D v •
          (⟨Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1, hgen_mem v⟩ :
            Divisor.degZero (K := K) (F := F)) := by
      apply Subtype.ext
      rw [AddSubgroup.val_finsetSum]
      simp only [AddSubgroupClass.coe_zsmul]
      exact hDiv.symm
    rw [hDeq]
    change QuotientAddGroup.mk _ ∈ _
    rw [QuotientAddGroup.mk_sum]
    refine AddSubgroup.sum_mem _ fun v hv => ?_
    rw [QuotientAddGroup.mk_zsmul]
    have hvS : v ∉ S := fun hvS => (Finsupp.mem_support_iff.mp hv) (hS v hvS)
    exact AddSubgroup.zsmul_mem _ (hgen v hvS) _
  have hall := AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single hdeg1 V₀ x
  refine (AddSubgroup.closure_le (AddSubgroup.closure G)).mpr ?_ hall
  rintro _ ⟨V, hVdeg, rfl⟩
  by_cases hVS : V ∉ S
  · exact hgen V hVS
  push Not at hVS
  obtain ⟨f, hf0, hford⟩ :=
    AlgebraicCurve.Place.exists_forall_ord_eq S (fun w => if w = V then 1 else 0)
  obtain ⟨Pf, hPf, hPfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hPfmem : Pf ∈ Divisor.degZero (K := K) (F := F) := hPfdeg
  have hPfpr : Pic0.mk (⟨Pf, hPfmem⟩ : Divisor.degZero (K := K) (F := F)) = 0 := by
    change QuotientAddGroup.mk _ = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨f, hf0, hPf⟩
  have hD'mem : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 - Pf ∈
      Divisor.degZero (K := K) (F := F) :=
    sub_mem (hgen_mem V) hPfmem
  have hD'S : ∀ w ∈ S,
      (Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 - Pf : Divisor K F) w = 0 := by
    intro w hw
    have hwV₀ : w ≠ V₀ := fun h => hV₀ (h ▸ hw)
    rw [Finsupp.sub_apply, Finsupp.sub_apply, hPf w, hford w hw]
    by_cases hwV : w = V
    · subst hwV
      simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hwV₀, ite_true,
        sub_zero, sub_self]
    · simp only [Finsupp.single_eq_of_ne hwV, Finsupp.single_eq_of_ne hwV₀, ite_eq_right hwV,
        sub_self]
  have hsplit : (⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVdeg⟩ :
      Divisor.degZero (K := K) (F := F)) =
      ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 - Pf, hD'mem⟩ + ⟨Pf, hPfmem⟩ := by
    apply Subtype.ext
    exact (sub_add_cancel _ _).symm
  rw [hsplit, Pic0.mk_add, hPfpr, add_zero]
  exact key _ hD'mem hD'S

end JacobianVarieties.Pic0.Proofs.Pic0_mem_closure_mk_single_sub_single_of_notMem
end ProofImplementation

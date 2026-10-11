/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Cohomology.RiemannRoch.Ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional
import AlgebraicCurves.FunctionFields.CurveOver
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Degree-one divisor classes in genus one

Riemann--Roch supplies a nonzero section of every degree-one divisor. Its effective
divisor is a single place. The same dimension calculation proves uniqueness: a
function with at most one simple pole must be constant.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F]

/-- An effective divisor of degree one over an algebraically closed constant field
is the divisor of a single place. -/
theorem Divisor.exists_single_of_effective_degree_one (D : Divisor K F)
    (hD : ∀ v : Place K F, 0 ≤ D v) (hdegree : D.degree = 1) :
    ∃ p : Place K F, D = Finsupp.single p 1 := by
  classical
  have hsum : ∑ v ∈ D.support, D v = 1 := by
    have h := hdegree
    simp only [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum,
      AddMonoidHom.mulRight_apply,
      IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at h
    exact h
  have hsupport : D.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    omega
  obtain ⟨p, hp⟩ := hsupport
  have hp0 : D p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hp_le : D p ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun v _ => hD v) hp
  have hp1 : D p = 1 := by have := hD p; omega
  have herase : ∑ v ∈ D.support.erase p, D v = 0 := by
    have h := Finset.sum_erase_add D.support D hp
    rw [hsum, hp1] at h
    omega
  refine ⟨p, ?_⟩
  ext v
  by_cases hv : v = p
  · subst v
    rw [Finsupp.single_eq_same, hp1]
  · rw [Finsupp.single_eq_of_ne hv]
    by_cases hvD : v ∈ D.support
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hD w)).mp herase v
        (Finset.mem_erase.mpr ⟨hv, hvD⟩)
    · exact Finsupp.notMem_support_iff.mp hvD

variable [Algebra.EssFiniteType K F]

/-- In genus one, every degree-one divisor has exactly one independent section. -/
theorem ell_eq_one_of_genus_one_degree_one (hg : genusFF K F = 1)
    (D : Divisor K F) (hD : D.degree = 1) : ell D = 1 := by
  obtain ⟨t, ht, hfin, hsep⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional (K := K) (F := F)).mp
      (inferInstance : IsCurveOver K F)
  have hbound : 2 * (genusFF K F : ℤ) - 1 ≤ D.degree := by rw [hg, hD]; norm_num
  have h := ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
    K t ht hfin hsep D hbound
  rw [hg, hD] at h
  omega

/-- Two places on a genus-one function field cannot differ by a principal divisor
unless they are the same place. -/
theorem eq_of_single_sub_single_principal_of_genus_one (hg : genusFF K F = 1)
    (p q : Place K F) (h : Divisor.IsPrincipal (Finsupp.single p 1 - Finsupp.single q 1)) :
    p = q := by
  classical
  obtain ⟨f, hf, hord⟩ := h
  have hdim : ell (Finsupp.single q 1) = 1 :=
    ell_eq_one_of_genus_one_degree_one hg _ (by
      rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]; norm_num)
  have hnonneg : ∀ v : Place K F, 0 ≤ (Finsupp.single q (1 : ℤ)) v := by
    intro v
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  have hOne : (1 : F) ∈ LSpace (Finsupp.single q 1) :=
    lSpace_mono hnonneg one_mem_lSpace_zero
  have hfL : f ∈ LSpace (Finsupp.single q 1) := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr (fun v => ?_)
    rw [← hord v, Finsupp.sub_apply]
    have hp : 0 ≤ (Finsupp.single p (1 : ℤ)) v := by
      simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    omega
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    hdim hOne one_ne_zero
  rw [hspan] at hfL
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfL
  have hfZero : f ∈ LSpace (0 : Divisor K F) := by
    rw [← hc, Algebra.smul_def, mul_one]
    exact algebraMap_mem_lSpace_zero c
  have hnonnegative := ((mem_lSpace_iff_ord.mp hfZero).resolve_left hf) q
  by_contra hpq
  rw [← hord q, Finsupp.sub_apply, Finsupp.single_eq_of_ne (fun hqp => hpq hqp.symm),
    Finsupp.single_eq_same] at hnonnegative
  change -(0 : ℤ) ≤ 0 - 1 at hnonnegative
  omega

/-- Every degree-one divisor on a genus-one function field is linearly equivalent
to exactly one place. Neither an effective representative nor its uniqueness is input. -/
theorem existsUnique_place_principal_sub_of_genus_one (hg : genusFF K F = 1)
    (D : Divisor K F) (hD : D.degree = 1) :
    ∃! p : Place K F, Divisor.IsPrincipal (Finsupp.single p 1 - D) := by
  classical
  have hdim := ell_eq_one_of_genus_one_degree_one hg D hD
  have hne : LSpace D ≠ ⊥ := by
    intro h
    change Module.finrank K (LSpace D) = 1 at hdim
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨f, hfD, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hord := (mem_lSpace_iff_ord.mp hfD).resolve_left hf
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Df, hDf, hdegree⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have heff : ∀ v : Place K F, 0 ≤ (D + Df) v := by
    intro v
    rw [Finsupp.add_apply, hDf v]
    have := hord v
    omega
  have hdeg : (D + Df).degree = 1 := by rw [map_add, hD, hdegree, add_zero]
  obtain ⟨p, hp⟩ := Divisor.exists_single_of_effective_degree_one (D + Df) heff hdeg
  have hprincipal : Divisor.IsPrincipal (Finsupp.single p 1 - D) := by
    rw [← hp, add_sub_cancel_left]
    exact ⟨f, hf, hDf⟩
  refine ⟨p, hprincipal, ?_⟩
  intro q hq
  apply eq_of_single_sub_single_principal_of_genus_one hg q p
  have hsub := (Divisor.principal (K := K) (F := F)).sub_mem hq hprincipal
  rw [sub_sub_sub_cancel_right] at hsub
  exact hsub

end AlgebraicCurve

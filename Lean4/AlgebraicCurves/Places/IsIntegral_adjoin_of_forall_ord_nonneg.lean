/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Place_exists_of_valuationSubring
import AlgebraicCurves.Places.Place_ord_nonneg_of_mem
import AlgebraicCurves.Places.Place_mem_of_ord_nonneg

/-!
# Is Integral adjoin of forall ord nonneg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.IsIntegral_adjoin_of_forall_ord_nonneg

open AlgebraicCurve Polynomial

namespace INTGlue

theorem isIntegral_of_mem_adjoin_inv {A F : Type*} [CommRing A] [Field F] [Algebra A F]
    {z : F} (hz0 : z ≠ 0) (hmem : z ∈ Algebra.adjoin A ({z⁻¹} : Set F)) : IsIntegral A z := by
  classical
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hp' : aeval z⁻¹ p = z := hp
  have hdeg : (∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ (p.natDegree - i)).degree ≤
      (p.natDegree : WithBot ℕ) := by
    refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans (by exact_mod_cast Nat.sub_le _ _)
  refine ⟨X ^ (p.natDegree + 1) - ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^
    (p.natDegree - i),
    Polynomial.monic_X_pow_sub (hdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self _)), ?_⟩
  have hz : z = ∑ i ∈ Finset.range (p.natDegree + 1), algebraMap A F (p.coeff i) * z⁻¹ ^ i := by
    conv_lhs => rw [← hp']
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Algebra.smul_def]
  have hzpow : ∀ i ∈ Finset.range (p.natDegree + 1), z ^ p.natDegree * z⁻¹ ^ i = z ^ (p.natDegree -
    i) := by
    intro i hi
    have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
    rw [hk, Nat.add_sub_cancel_left, pow_add, mul_comm (z ^ i) (z ^ k), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hz0, one_pow, mul_one]
  rw [eval₂_sub, sub_eq_zero, eval₂_pow, eval₂_X, eval₂_finsetSum]
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [pow_succ]
  conv_lhs => arg 2; rw [hz]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_left_comm, hzpow i hi]

theorem isIntegral_of_forall_valuationSubring {F : Type*} [Field F] (A : Subring F) (z : F)
    (h : ∀ V : ValuationSubring F, A ≤ V.toSubring → z ∈ V) : IsIntegral A z := by
  classical
  by_contra hnot
  have hz0 : z ≠ 0 := by rintro rfl; exact hnot isIntegral_zero
  set y : F := z⁻¹ with hy
  let B : Subalgebra A F := Algebra.adjoin A ({y} : Set F)
  have hyB : y ∈ B := Algebra.subset_adjoin (Set.mem_singleton y)
  have hzB : z ∉ B := fun hzB => hnot (isIntegral_of_mem_adjoin_inv hz0 hzB)
  have hyu : (⟨y, hyB⟩ : B) ∈ nonunits B := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have hinv : ((u⁻¹ : Bˣ) : B).1 = z := by
      have h1 : ((u : B) : F) * ((u⁻¹ : Bˣ) : B) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
      rw [hu] at h1
      have : y⁻¹ = ((u⁻¹ : Bˣ) : B).1 := inv_eq_of_mul_eq_one_right h1
      rw [← this, hy, inv_inv]
    exact hzB (hinv ▸ ((u⁻¹ : Bˣ) : B).2)
  obtain ⟨m, hm, hym⟩ := exists_max_ideal_of_mem_nonunits hyu
  let Bs : Subring F := B.toSubring
  let m' : Ideal Bs := m
  have : m'.IsMaximal := hm
  let L : LocalSubring F := LocalSubring.ofPrime Bs m'
  obtain ⟨V, hV⟩ := L.exists_le_valuationSubring
  obtain ⟨hLV, hloc⟩ := LocalSubring.le_def.mp hV
  have hBL : Bs ≤ L.toSubring := LocalSubring.le_ofPrime Bs m'
  have hAV : A ≤ V.toSubring := by
    intro a ha
    have : (a : F) ∈ Bs := by
      change a ∈ B
      exact Subalgebra.algebraMap_mem B ⟨a, ha⟩
    exact hLV (hBL this)
  have hzV : z ∈ V := h V hAV
  have hyL : (algebraMap Bs L.toSubring ⟨y, hyB⟩) ∈ IsLocalRing.maximalIdeal L.toSubring :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L.toSubring m' ⟨y, hyB⟩).mpr hym
  have hcoe : ((algebraMap Bs L.toSubring ⟨y, hyB⟩ : L.toSubring) : F) = y := by
    change algebraMap L.toSubring F (algebraMap Bs L.toSubring ⟨y, hyB⟩) = y
    rw [← IsScalarTower.algebraMap_apply Bs L.toSubring F]
    rfl
  have hyV' : ¬ IsUnit (Subring.inclusion hLV (algebraMap Bs L.toSubring ⟨y, hyB⟩)) := by
    intro hu
    have := (IsLocalRing.mem_maximalIdeal _).mp hyL
    exact this (hloc.map_nonunit _ hu)
  apply hyV'
  have hyVmem : y ∈ V := by
    have := (Subring.inclusion hLV (algebraMap Bs L.toSubring ⟨y, hyB⟩)).2
    rwa [Subring.coe_inclusion, hcoe] at this
  refine isUnit_iff_exists_inv.mpr ⟨⟨z, hzV⟩, ?_⟩
  ext
  simp only [Subring.coe_mul, Subring.coe_inclusion, hcoe, Subring.coe_one]
  rw [hy, inv_mul_cancel₀ hz0]

end INTGlue

theorem _root_.AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg {K F : Type*} [Field K] [Field
  F] [Algebra K F] [CharZero K] (t : F)
    (_ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [AlgebraicCurve.HasPrincipalDivisors K F] (z : F)
    (hz : ∀ v : AlgebraicCurve.Place K F, 0 ≤ v.ord t → 0 ≤ v.ord z) :
    IsIntegral (Algebra.adjoin K ({t} : Set F)) z := by
  classical
  have key : IsIntegral (Algebra.adjoin K ({t} : Set F)).toSubring z := by
    refine INTGlue.isIntegral_of_forall_valuationSubring _ z fun V hV => ?_
    by_cases hz0 : z = 0
    · rw [hz0]; exact V.zero_mem
    by_cases htop : V = ⊤
    · rw [htop]; exact ValuationSubring.mem_top z
    have hK : ∀ a : K, algebraMap K F a ∈ V := fun a =>
      hV (Subalgebra.algebraMap_mem (Algebra.adjoin K ({t} : Set F)) a)
    obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_of_valuationSubring t V hK htop
    have htV : t ∈ v.toValuationSubring := by
      rw [hv]; exact hV (Algebra.subset_adjoin (Set.mem_singleton t))
    have h1 : 0 ≤ v.ord t := v.ord_nonneg_of_mem htV
    have h2 := AlgebraicCurve.Place.mem_of_ord_nonneg v hz0 (hz v h1)
    rwa [hv] at h2
  exact key
end AlgebraicCurves.Places.Proofs.IsIntegral_adjoin_of_forall_ord_nonneg
end ProofImplementation

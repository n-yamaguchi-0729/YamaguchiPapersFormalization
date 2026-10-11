/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Evaluation
import Mathlib.Algebra.BigOperators.Field
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Rational.RationalFunctionField_deg_eq_one_of_isAlgClosed
import AlgebraicCurves.Places.Place_isRational_iff_deg_eq_one
import AlgebraicCurves.Places.Place_mem_of_ord_nonneg

/-!
# Place is Rational of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_isRational_of_isAlgClosed

open AlgebraicCurve Polynomial

theorem _root_.AlgebraicCurve.Place.isRational_of_isAlgClosed {K F : Type*} [Field K] [IsAlgClosed
  K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] (v : Place K F) : v.IsRational := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  let u : Place K (RatFunc K) := v.restrict (RatFunc K)
  have hu : u.IsRational :=
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one u).2
      (AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed K u)
  have hconst : ∀ {b : RatFunc K} (hb : algebraMap (RatFunc K) F b ∈ v.toValuationSubring),
      ∃ c : K, algebraMap K v.ResidueField c
        = IsLocalRing.residue _ (⟨algebraMap (RatFunc K) F b, hb⟩ : v.toValuationSubring) := by
    intro b hb
    have hb' : b ∈ u.toValuationSubring := ValuationSubring.mem_comap.mpr hb
    refine ⟨u.evalAt b, ?_⟩
    have h1 : algebraMap K u.ResidueField (u.evalAt b) = IsLocalRing.residue _ ⟨b, hb'⟩ :=
      u.algebraMap_evalAt hu hb'
    have h2 : (⟨algebraMap (RatFunc K) F b, hb⟩ : v.toValuationSubring)
        = Place.restrictInclusion (RatFunc K) v ⟨b, hb'⟩ := rfl
    rw [h2, ← Place.restrictResidueMap_residue, ← h1, ← Place.algebraMap_residueField_eq,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨p, hp0, hpx⟩ : IsAlgebraic (RatFunc K) (x : F) := Algebra.IsAlgebraic.isAlgebraic _
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨j, hj, hjmin⟩ := p.support.exists_min_image
    (fun i => v.ord (algebraMap (RatFunc K) F (p.coeff i))) hsupp
  have haj0 : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hajF : algebraMap (RatFunc K) F (p.coeff j) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) F).injective).mpr haj0
  have hbmem : ∀ i, algebraMap (RatFunc K) F (p.coeff i / p.coeff j) ∈ v.toValuationSubring := by
    intro i
    by_cases hi : i ∈ p.support
    · have hai0 : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
      have haiF : algebraMap (RatFunc K) F (p.coeff i) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap (RatFunc K) F).injective).mpr hai0
      rw [map_div₀]
      refine v.mem_of_ord_nonneg (div_ne_zero haiF hajF) ?_
      rw [div_eq_mul_inv, v.ord_mul haiF (inv_ne_zero hajF), v.ord_inv]
      have := hjmin i hi
      omega
    · rw [Polynomial.notMem_support_iff.mp hi, zero_div, map_zero]
      exact zero_mem _
  have haeval : ∀ (q : (RatFunc K)[X]) (z : F),
      aeval z q = ∑ i ∈ q.support, algebraMap (RatFunc K) F (q.coeff i) * z ^ i := by
    intro q z
    conv_lhs => rw [q.as_sum_support]
    simp [map_sum, ← C_mul_X_pow_eq_monomial]
  have hrel : ∑ i ∈ p.support,
      algebraMap (RatFunc K) F (p.coeff i / p.coeff j) * (x : F) ^ i = 0 := by
    have hsum : ∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i) * (x : F) ^ i = 0 := by
      rw [← haeval, hpx]
    have hfac : ∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i / p.coeff j) * (x : F) ^ i
        = (∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i) * (x : F) ^ i)
            / algebraMap (RatFunc K) F (p.coeff j) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_div₀]
      ring
    rw [hfac, hsum, zero_div]
  set B : ℕ → v.toValuationSubring := fun i => ⟨_, hbmem i⟩ with hB
  have hrelO : ∑ i ∈ p.support, B i * x ^ i = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      ZeroMemClass.coe_zero, hB]
    exact hrel
  choose c hc using fun i => hconst (hbmem i)
  have hcj : c j = 1 := by
    have h1 : (B j) = 1 := Subtype.ext (by simp [hB, haj0])
    have := hc j
    rw [show (⟨_, hbmem j⟩ : v.toValuationSubring) = B j from rfl, h1, map_one] at this
    exact (algebraMap K v.ResidueField).injective (by rw [this, map_one])
  set R : K[X] := ∑ i ∈ p.support, C (c i) * X ^ i with hR
  have hRy : aeval (IsLocalRing.residue v.toValuationSubring x) R = 0 := by
    have h := congrArg (IsLocalRing.residue v.toValuationSubring) hrelO
    rw [map_sum, map_zero] at h
    simp only [map_mul, map_pow] at h
    rw [hR, map_sum]
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i]
  have hRj : R.coeff j = 1 := by
    rw [hR, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq p.support j, ite_eq_left hj, hcj]
  have hR0 : R ≠ 0 := fun h => by
    have := hRj
    rw [h, coeff_zero] at this
    exact zero_ne_one this
  have halgy : IsAlgebraic K (IsLocalRing.residue v.toValuationSubring x) := ⟨R, hR0, hRy⟩
  have hdeg : (minpoly K (IsLocalRing.residue v.toValuationSubring x)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halgy.isIntegral)
  obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
  exact ⟨a, ha⟩
end AlgebraicCurves.Places.Proofs.Place_isRational_of_isAlgClosed
end ProofImplementation

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

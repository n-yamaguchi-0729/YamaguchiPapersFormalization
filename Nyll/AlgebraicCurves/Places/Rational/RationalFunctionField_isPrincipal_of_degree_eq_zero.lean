/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.RatFunc.Degree
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Divisors.Divisor_degree_eq_sum
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import Mathlib.FieldTheory.RatFunc.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Rational Function Field is Principal of degree eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_isPrincipal_of_degree_eq_zero
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open _root_.Polynomial

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace RationalFunctionField
open _root_.AlgebraicCurve.RationalFunctionField
namespace W2B
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.AlgebraicCurve

variable {K : Type*} [Field K]

theorem ord_prod {F : Type*} [Field F] [Algebra K F] (v : Place K F) {ι : Type*} (s : Finset ι)
    (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg a (Finset.mem_cons_self ..))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_cons_of_mem hi)]

/-- The condition that a rational-function place comes from a height-one prime of the
polynomial ring. -/
abbrev IsFinite (v : Place K (RatFunc K)) : Prop :=
  ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w

/-- A height-one prime representing the given finite rational-function place. -/
def spec {v : Place K (RatFunc K)} (hv : IsFinite v) : HeightOneSpectrum K[X] := hv.choose

theorem eq_ofHeightOneSpectrum_spec {v : Place K (RatFunc K)} (hv : IsFinite v) :
    v = Place.ofHeightOneSpectrum (spec hv) := hv.choose_spec

open Classical in
/-- A generator of the prime of a finite place, with polynomial one assigned at infinity. -/
def gen (v : Place K (RatFunc K)) : K[X] :=
  if hv : IsFinite v then Submodule.IsPrincipal.generator (spec hv).asIdeal else 1

theorem span_gen {v : Place K (RatFunc K)} (hv : IsFinite v) :
    (spec hv).asIdeal = Ideal.span {gen v} := by
  simp only [gen, dite_eq_left hv]
  exact (Ideal.span_singleton_generator _).symm

theorem gen_of_not_isFinite {v : Place K (RatFunc K)} (hv : ¬ IsFinite v) : gen v = 1 := by
  simp only [gen, dite_eq_right hv]

theorem gen_ne_zero (v : Place K (RatFunc K)) : gen v ≠ 0 := by
  by_cases hv : IsFinite v
  · intro h
    exact (spec hv).ne_bot (by rw [span_gen hv, h, Ideal.span_singleton_eq_bot])
  · rw [gen_of_not_isFinite hv]; exact one_ne_zero

theorem algebraMap_gen_ne_zero (v : Place K (RatFunc K)) :
    algebraMap K[X] (RatFunc K) (gen v) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (gen_ne_zero v)

open Classical in
theorem ord_gen_of_isFinite {u : Place K (RatFunc K)} (hu : IsFinite u) (v : Place K (RatFunc K)) :
    u.ord (algebraMap K[X] (RatFunc K) (gen v)) = if v = u then 1 else 0 := by
  classical
  by_cases hvu : v = u
  · subst hvu
    rw [ite_eq_left rfl]
    have h := ord_ofHeightOneSpectrum_of_span (spec hu) (gen_ne_zero v) (span_gen hu)
    rwa [← eq_ofHeightOneSpectrum_spec hu] at h
  rw [ite_eq_right hvu]
  by_cases hv : IsFinite v
  · by_contra hne
    rw [eq_ofHeightOneSpectrum_spec hu] at hne
    have hmem : gen v ∈ (spec hu).asIdeal :=
      (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) (spec hu)
        (gen_ne_zero v)).mp hne
    have hle : (spec hv).asIdeal ≤ (spec hu).asIdeal := by
      rw [span_gen hv, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have heq : (spec hv).asIdeal = (spec hu).asIdeal :=
      (spec hv).isMaximal.eq_of_le (spec hu).isPrime.ne_top hle
    exact hvu (by rw [eq_ofHeightOneSpectrum_spec hv, eq_ofHeightOneSpectrum_spec hu,
      HeightOneSpectrum.ext heq])
  · rw [gen_of_not_isFinite hv, map_one, Place.ord_one]

open Classical in
theorem ord_gen_of_not_isFinite {u : Place K (RatFunc K)} (hu : ¬ IsFinite u)
    (v : Place K (RatFunc K)) :
    u.ord (algebraMap K[X] (RatFunc K) (gen v)) = -(v.deg : ℤ) + if v = u then 1 else 0 := by
  classical
  have hu' : ∀ w : HeightOneSpectrum K[X], u ≠ Place.ofHeightOneSpectrum w :=
    fun w h => hu ⟨w, h⟩
  by_cases hv : IsFinite v
  · have hvu : v ≠ u := fun h => hu (h ▸ hv)
    rw [ite_eq_right hvu, add_zero,
      ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum u hu' (algebraMap_gen_ne_zero v),
      RatFunc.intDegree_polynomial]
    conv_rhs => rw [eq_ofHeightOneSpectrum_spec hv, deg_ofHeightOneSpectrum K (span_gen hv)]
  · have hv' : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w :=
      fun w h => hv ⟨w, h⟩
    have hvu : v = u := subsingleton_setOf_forall_ne_ofHeightOneSpectrum hv' hu'
    rw [ite_eq_left hvu, gen_of_not_isFinite hv, map_one, Place.ord_one,
      deg_eq_one_of_forall_ne_ofHeightOneSpectrum v hv']
    norm_num

/-- The rational-function factor obtained by raising the place generator to its divisor
coefficient. -/
def genFactor (D : Divisor K (RatFunc K)) (v : Place K (RatFunc K)) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (gen v) ^ (D v)

theorem genFactor_ne_zero (D : Divisor K (RatFunc K)) (v : Place K (RatFunc K)) :
    genFactor D v ≠ 0 :=
  zpow_ne_zero _ (algebraMap_gen_ne_zero v)

theorem isPrincipal_of_degree_eq_zero' (D : Divisor K (RatFunc K)) (hD : Divisor.degree D = 0) :
    D.IsPrincipal := by
  classical
  refine ⟨∏ v ∈ D.support, genFactor D v,
    Finset.prod_ne_zero_iff.mpr fun v _ => genFactor_ne_zero D v, fun u => ?_⟩
  rw [ord_prod u _ _ fun v _ => genFactor_ne_zero D v]
  have hfactor : ∀ v : Place K (RatFunc K),
      u.ord (genFactor D v) = D v * u.ord (algebraMap K[X] (RatFunc K) (gen v)) := by
    intro v
    rw [genFactor, u.ord_zpow]
  have hdeg : ∑ v ∈ D.support, D v * (v.deg : ℤ) = 0 := by
    rw [← Divisor.degree_eq_sum D, hD]
  by_cases hu : IsFinite u
  · have hcong : ∀ v ∈ D.support, u.ord (genFactor D v) = if v = u then D u else 0 := by
      intro v _
      rw [hfactor v, ord_gen_of_isFinite hu v]
      by_cases hvu : v = u
      · rw [ite_eq_left hvu, ite_eq_left hvu, hvu, mul_one]
      · rw [ite_eq_right hvu, ite_eq_right hvu, mul_zero]
    rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq']
    by_cases hmem : u ∈ D.support
    · rw [ite_eq_left hmem]
    · simp [Finsupp.notMem_support_iff.mp hmem]
  · have hcong : ∀ v ∈ D.support, u.ord (genFactor D v)
        = -(D v * (v.deg : ℤ)) + (if v = u then D v else 0) := by
      intro v _
      rw [hfactor v, ord_gen_of_not_isFinite hu v]
      by_cases hv : v = u
      · rw [ite_eq_left hv, ite_eq_left hv]; ring
      · rw [ite_eq_right hv, ite_eq_right hv]; ring
    rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib, Finset.sum_neg_distrib, hdeg,
      neg_zero, zero_add, Finset.sum_ite_eq']
    by_cases hmem : u ∈ D.support
    · rw [ite_eq_left hmem]
    · simp [Finsupp.notMem_support_iff.mp hmem]

end AlgebraicCurve.RationalFunctionField.W2B

end

open _root_.AlgebraicCurve AlgebraicCurve in
theorem _root_.AlgebraicCurve.RationalFunctionField.isPrincipal_of_degree_eq_zero {K : Type*}
  [Field K] (D : Divisor K (RatFunc K)) (hD : Divisor.degree D = 0) : D.IsPrincipal :=
  AlgebraicCurve.RationalFunctionField.W2B.isPrincipal_of_degree_eq_zero' D hD
end AlgebraicCurves.Places.Rational.Proofs.RationalFunctionField_isPrincipal_of_degree_eq_zero
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Place mem to Valuation Subring of eval Eval eq zero of eval leading Coeff ne zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero

open _root_.AlgebraicCurve
open _root_.Polynomial
open _root_.IsLocalRing
open scoped Polynomial.Bivariate

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem g2p_algebraMap_comp :
    (algebraMap v.toValuationSubring F).comp (algebraMap K v.toValuationSubring) = algebraMap K F :=
  (IsScalarTower.algebraMap_eq K v.toValuationSubring F).symm

private theorem _root_.AlgebraicCurve.Place.g2p_hom_evalEval {S : Type*} [CommRing S] (φ :
  v.toValuationSubring →+* S)
    (P : K[X][Y]) (a b : v.toValuationSubring) :
    φ ((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b)
      = (P.map (mapRingHom (φ.comp (algebraMap K v.toValuationSubring)))).evalEval (φ a) (φ b) := by
  rw [← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp]

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.g2p_hom_eval {S : Type*} [CommRing S] (φ :
  v.toValuationSubring →+* S)
    (p : K[X]) (a : v.toValuationSubring) :
    φ ((p.map (algebraMap K v.toValuationSubring)).eval a)
      = (p.map (φ.comp (algebraMap K v.toValuationSubring))).eval (φ a) := by
  rw [eval_map, eval_map, hom_eval₂]

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.g2p_coe_evalEval (P : K[X][Y]) (a b :
  v.toValuationSubring) :
    (((P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval a b : v.toValuationSubring)
      : F)
      = (P.map (mapRingHom (algebraMap K F))).evalEval (a : F) (b : F) := by
  have h := v.g2p_hom_evalEval (algebraMap v.toValuationSubring F) P a b
  rw [g2p_algebraMap_comp] at h
  exact h

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.g2p_coe_eval (p : K[X]) (a : v.toValuationSubring) :
    (((p.map (algebraMap K v.toValuationSubring)).eval a : v.toValuationSubring) : F)
      = (p.map (algebraMap K F)).eval (a : F) := by
  have h := v.g2p_hom_eval (algebraMap v.toValuationSubring F) p a
  rw [g2p_algebraMap_comp] at h
  exact h

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.g2p_evalEval_mem (P : K[X][Y]) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    (P.map (mapRingHom (algebraMap K F))).evalEval z y ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_evalEval P ⟨z, hz⟩ ⟨y, hy⟩]
  exact SetLike.coe_mem _

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.g2p_eval_mem (p : K[X]) {z : F} (hz : z ∈
  v.toValuationSubring) :
    (p.map (algebraMap K F)).eval z ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_eval p ⟨z, hz⟩]
  exact SetLike.coe_mem _

open _root_.AlgebraicCurve.Place

theorem g2p_algebraMap_residueField (c : K) :
    algebraMap K v.ResidueField c
      = residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    ResidueField.algebraMap_eq]

private theorem _root_.AlgebraicCurve.Place.g2p_residue_mk (hv : v.IsRational) (a :
  v.toValuationSubring) :
    residue v.toValuationSubring a = algebraMap K v.ResidueField (v.evalAt (a : F)) := by
  rw [v.algebraMap_evalAt hv a.2]

open _root_.AlgebraicCurve.Place

private theorem _root_.AlgebraicCurve.Place.g2p_evalAt_evalEval (hv : v.IsRational) (P : K[X][Y])
  {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    v.evalAt ((P.map (mapRingHom (algebraMap K F))).evalEval z y)
      = P.evalEval (v.evalAt z) (v.evalAt y) := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.g2p_evalEval_mem P hz hy)]
  have hmk : (⟨(P.map (mapRingHom (algebraMap K F))).evalEval z y, v.g2p_evalEval_mem P hz hy⟩
        : v.toValuationSubring)
      = (P.map (mapRingHom (algebraMap K v.toValuationSubring))).evalEval ⟨z, hz⟩ ⟨y, hy⟩ :=
    Subtype.ext (by rw [g2p_coe_evalEval])
  rw [hmk, ← ResidueField.algebraMap_eq, g2p_hom_evalEval,
    ← IsScalarTower.algebraMap_eq K v.toValuationSubring v.ResidueField,
    ResidueField.algebraMap_eq, v.g2p_residue_mk hv, v.g2p_residue_mk hv,
    map_mapRingHom_evalEval]

open _root_.AlgebraicCurve.Place
private theorem _root_.AlgebraicCurve.Place.g2p_evalAt_eval (hv : v.IsRational) (p : K[X]) {z : F}
  (hz : z ∈ v.toValuationSubring) :
    v.evalAt ((p.map (algebraMap K F)).eval z) = p.eval (v.evalAt z) := by
  have h := v.g2p_evalAt_evalEval hv (C p) hz hz
  rwa [Polynomial.map_C, evalEval_C, evalEval_C] at h

open _root_.AlgebraicCurve.Place

theorem g2p_sub_mem_maximalIdeal (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
  rw [← residue_eq_zero_iff, map_sub, ← g2p_algebraMap_residueField, v.g2p_residue_mk hv, sub_self]

theorem g2p_isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have hab : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have ha' : a ∈ maximalIdeal R := by simpa using sub_mem hab hb
  exact (IsLocalRing.mem_maximalIdeal _).mp ha' ha

end AlgebraicCurve.Place

end Place_mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero
end AlgebraicCurves.Places.Proofs

namespace AlgebraicCurve.Place

open _root_.AlgebraicCurve
open _root_.Polynomial
open _root_.IsLocalRing
open scoped Polynomial.Bivariate

theorem mem_toValuationSubring_of_evalEval_eq_zero_of_eval_leadingCoeff_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F} (hz : z ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hlead : G.leadingCoeff.eval (v.evalAt z) ≠ 0) :
    y ∈ v.toValuationSubring := by
  by_contra hyO
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyO (zero_mem _)
  have hvy : 1 < v.toValuationSubring.valuation y := by
    rw [← not_le, ValuationSubring.valuation_le_one_iff]
    exact hyO
  have hvy0 : v.toValuationSubring.valuation y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
  set c : ℕ → F := fun i => ((G.coeff i).map (algebraMap K F)).eval z with hc
  have hc_mem : ∀ i, c i ∈ v.toValuationSubring := fun i => v.g2p_eval_mem (G.coeff i) hz
  have hc_le : ∀ i, v.toValuationSubring.valuation (c i) ≤ 1 := fun i =>
    (ValuationSubring.valuation_le_one_iff _ _).mpr (hc_mem i)
  have hsum : (G.map (mapRingHom (algebraMap K F))).evalEval z y
      = ∑ i ∈ Finset.range (G.natDegree + 1), c i * y ^ i := by
    have hn : (G.map (mapRingHom (algebraMap K F))).natDegree < G.natDegree + 1 :=
      Nat.lt_succ_of_le natDegree_map_le
    unfold Polynomial.evalEval
    rw [eval_eq_sum_range' hn, eval_finsetSum]
    simp only [eval_mul, eval_pow, eval_C, coeff_map, hc]
    rfl
  rw [hsum, Finset.sum_range_succ] at hG
  have hcd : v.toValuationSubring.valuation (c G.natDegree) = 1 := by
    have hval : v.evalAt (c G.natDegree) ≠ 0 := by
      rw [hc, v.g2p_evalAt_eval hv _ hz, coeff_natDegree]
      exact hlead
    have hunit : IsUnit (⟨c G.natDegree, hc_mem _⟩ : v.toValuationSubring) := by
      rw [← residue_ne_zero_iff_isUnit, v.g2p_residue_mk hv]
      exact (_root_.map_ne_zero _).mpr hval
    simpa using (ValuationSubring.valuation_eq_one_iff _ _).mp hunit
  have heq : c G.natDegree * y ^ G.natDegree
      = -∑ i ∈ Finset.range G.natDegree, c i * y ^ i := eq_neg_of_add_eq_zero_right hG
  have h1 : v.toValuationSubring.valuation (c G.natDegree * y ^ G.natDegree)
      = v.toValuationSubring.valuation y ^ G.natDegree := by
    rw [map_mul, map_pow, hcd, one_mul]
  have h2 : v.toValuationSubring.valuation (-∑ i ∈ Finset.range G.natDegree, c i * y ^ i)
      < v.toValuationSubring.valuation y ^ G.natDegree := by
    rw [Valuation.map_neg]
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hvy0)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc v.toValuationSubring.valuation (c i) * v.toValuationSubring.valuation y ^ i
        ≤ 1 * v.toValuationSubring.valuation y ^ i := mul_le_mul' (hc_le i) le_rfl
      _ = v.toValuationSubring.valuation y ^ i := one_mul _
      _ < v.toValuationSubring.valuation y ^ G.natDegree := pow_lt_pow_right₀ hvy hi
  rw [← heq, h1] at h2
  exact lt_irrefl _ h2

end AlgebraicCurve.Place
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ord_sub_algebraMap_evalAt_eq_one_of_derivative_evalEval_ne_zero_of_ord_sub_algebraMap_evalAt_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Nyll.AlgebraicCurves.Places.Place_ord_nonneg_of_mem
import Nyll.AlgebraicCurves.Places.Place_exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero

/-!
# Place ord sub algebra Map eval At eq one of derivative eval Eval ne zero of ord sub
algebra Map eval At eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.UniformizerDerivativeOrder

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
theorem g2p_eval_mem (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    (p.map (algebraMap K F)).eval z ∈ v.toValuationSubring := by
  rw [← v.g2p_coe_eval p ⟨z, hz⟩]
  exact SetLike.coe_mem _

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
theorem g2p_evalAt_eval (hv : v.IsRational) (p : K[X]) {z : F} (hz : z ∈ v.toValuationSubring) :
    v.evalAt ((p.map (algebraMap K F)).eval z) = p.eval (v.evalAt z) := by
  have h := v.g2p_evalAt_evalEval hv (C p) hz hz
  rwa [Polynomial.map_C, evalEval_C, evalEval_C] at h

private theorem _root_.AlgebraicCurve.Place.g2p_sub_mem_maximalIdeal (hv : v.IsRational) {f : F}
  (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
  rw [← residue_eq_zero_iff, map_sub, ← g2p_algebraMap_residueField, v.g2p_residue_mk hv, sub_self]

open _root_.AlgebraicCurve.Place

theorem g2p_isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have hab : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have ha' : a ∈ maximalIdeal R := by simpa using sub_mem hab hb
  exact (IsLocalRing.mem_maximalIdeal _).mp ha' ha

end AlgebraicCurve.Place

open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.Polynomial
open _root_.IsLocalRing
end AlgebraicCurves.Places.Proofs.UniformizerDerivativeOrder

namespace AlgebraicCurve.Place

open _root_.AlgebraicCurves.Places.Proofs.UniformizerDerivativeOrder
open _root_.AlgebraicCurve
open _root_.Polynomial
open _root_.IsLocalRing
open scoped _root_.Polynomial.Bivariate
open _root_.AlgebraicCurve.Place


theorem
 ord_sub_algebraMap_evalAt_eq_one_of_derivative_evalEval_ne_zero_of_ord_sub_algebraMap_evalAt_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {z y : F} (hz : z ∈ v.toValuationSubring)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (hy1 : v.ord (y - algebraMap K F (v.evalAt y)) = 1) :
    v.ord (z - algebraMap K F (v.evalAt z)) = 1 := by
  have hne : y - algebraMap K F (v.evalAt y) ≠ 0 := by
    intro h
    rw [h, ord_zero] at hy1
    exact zero_ne_one hy1
  have hmem : y - algebraMap K F (v.evalAt y) ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt hne (by rw [hy1]; exact zero_le_one)
  have hy : y ∈ v.toValuationSubring := by
    simpa using add_mem hmem (v.algebraMap_mem' (v.evalAt y))
  obtain ⟨h, hh, heq⟩ :=
    v.exists_sub_algebraMap_evalAt_eq_mul_of_derivative_evalEval_ne_zero hv hz hy G hG hsep
  have hzne : z - algebraMap K F (v.evalAt z) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at heq
    exact hne heq
  have hhne : h ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at heq
    exact hne heq
  have hordh : 0 ≤ v.ord h := v.ord_nonneg_of_mem hh
  have hzmem : z - algebraMap K F (v.evalAt z) ∈ v.toValuationSubring :=
    sub_mem hz (v.algebraMap_mem' _)
  have hordz : 1 ≤ v.ord (z - algebraMap K F (v.evalAt z)) := by
    rcases (v.ord_nonneg_of_mem hzmem).lt_or_eq with hlt | heq0
    · exact hlt
    · exfalso
      have hu := v.isUnit_mk_of_ord_eq_zero hzne heq0.symm
      have hm : (⟨z - algebraMap K F (v.evalAt z), hzmem⟩ : v.toValuationSubring)
          ∈ maximalIdeal v.toValuationSubring := by
        have := v.g2p_sub_mem_maximalIdeal hv hz
        convert this using 1
        rfl
      exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  rw [heq, v.ord_mul hhne hzne] at hy1
  omega

end AlgebraicCurve.Place
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.CharZero.Infinite
import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Nyll.AlgebraicCurves.FunctionFields.FiniteDimensional_adjoin_of_transcendental
import Nyll.AlgebraicCurves.Divisors.HasPrincipalDivisors_of_transcendental
import Nyll.AlgebraicCurves.Places.Place_exists_integralClosureAt_of_ord_fiber_nonneg
import Nyll.AlgebraicCurves.Places.Place_ord_nonneg_of_mem

/-!
# Place eval leading Coeff ne zero of forall mem to Valuation Subring
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint


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
open _root_.Polynomial
open _root_.IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

section absolute
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.rfg_evalAt_sub_algebraMap (hv : v.IsRational) {y : F}
  (hy : y ∈ v.toValuationSubring) (c : K) :
    v.evalAt (y - algebraMap K F c) = v.evalAt y - c := by
  have h := v.g2p_evalAt_eval hv (X - C c) hy
  simpa [Polynomial.map_sub] using h

open _root_.AlgebraicCurve.Place

private theorem _root_.AlgebraicCurve.Place.rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne (hv :
  v.IsRational) {y : F}
    (hy : y ∈ v.toValuationSubring) {c : K} (hc : v.evalAt y ≠ c) :
    v.ord (y - algebraMap K F c) = 0 := by
  have hmem : y - algebraMap K F c ∈ v.toValuationSubring := sub_mem hy (v.algebraMap_mem' c)
  have hval : v.evalAt (y - algebraMap K F c) ≠ 0 := by
    rw [v.rfg_evalAt_sub_algebraMap hv hy]
    exact sub_ne_zero.mpr hc
  have hunit : IsUnit (⟨y - algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    rw [← residue_ne_zero_iff_isUnit, v.g2p_residue_mk hv]
    exact (_root_.map_ne_zero _).mpr hval
  exact v.ord_coe_unit hunit.unit

open _root_.AlgebraicCurve.Place

private theorem _root_.AlgebraicCurve.Place.rfg_ord_sub_algebraMap_pos (hv : v.IsRational) {y : F}
    (hy : y ∈ v.toValuationSubring) {c : K} (h : v.evalAt y = c) (h0 : y ≠ algebraMap K F c) :
    0 < v.ord (y - algebraMap K F c) := by
  have hmem : y - algebraMap K F c ∈ v.toValuationSubring := sub_mem hy (v.algebraMap_mem' c)
  have hmax : (⟨y - algebraMap K F c, hmem⟩ : v.toValuationSubring)
      ∈ maximalIdeal v.toValuationSubring := by
    have := v.g2p_sub_mem_maximalIdeal hv hy
    rw [h] at this
    convert this using 1
    rfl
  exact (v.mem_maximalIdeal_iff_ord_pos (sub_ne_zero.mpr h0) hmem).mp hmax

open _root_.AlgebraicCurve.Place
end absolute

section tower
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F']

omit [Algebra K F] [IsScalarTower K F F'] in
theorem rfg_ramificationIndex_eq_one_of_ord_eq_one [Algebra.IsIntegral F F'] (w : Place K F')
    {t : F} (ht : w.ord (algebraMap F F' t) = 1) : w.ramificationIndex F = 1 := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero, ord_zero] at ht
    exact zero_ne_one ht
  have h1 := w.ramificationIndex_le_ord (F := F) ht0 (by rw [ht]; exact one_pos)
  have h2 := w.ramificationIndex_pos (F := F)
  rw [ht] at h1
  omega

theorem rfg_inertiaDeg_eq_one_of_isRational [Algebra.IsIntegral F F'] (w : Place K F')
    (hw : w.IsRational) : w.inertiaDeg F = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [deg_eq_one_of_isRational hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

end tower

end AlgebraicCurve.Place

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

theorem rf_gauss_minpoly {K F : Type*} [Field K] [Field F] [Algebra K F]
    {z : F} (hz : Transcendental K z) (y : F)
    [FiniteDimensional (IntermediateField.adjoin K ({z} : Set F)) F]
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (c : IntermediateField.adjoin K ({z} : Set F)) :
    ((G.map (Polynomial.mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
        (evalRingHom (⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ :
          IntermediateField.adjoin K ({z} : Set F)))).eval c
      = ((G.leadingCoeff).map (algebraMap K (IntermediateField.adjoin K ({z} : Set F)))).eval
            ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
        * (minpoly (IntermediateField.adjoin K ({z} : Set F)) y).eval c := by
  set zz : IntermediateField.adjoin K ({z} : Set F) :=
    ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩ with hzzdef
  have hzzF : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F zz = z := rfl
  set φ : K[X] →+* IntermediateField.adjoin K ({z} : Set F) :=
    (evalRingHom zz).comp (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))
    with hφdef
  have hφapply : ∀ p : K[X], φ p = aeval zz p := by
    intro p
    simp only [hφdef, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_evalRingHom,
      eval_map_algebraMap]
  have hψ : ∀ p : K[X], RatFunc.algEquivOfTranscendental z hz (algebraMap K[X] (RatFunc K) p) = φ p
    := by
    intro p
    rw [RatFunc.algEquivOfTranscendental_algebraMap, hφapply]
    rfl
  have hφinj : Function.Injective φ := by
    intro p q hpq
    rw [← hψ, ← hψ] at hpq
    exact IsFractionRing.injective K[X] (RatFunc K)
      ((RatFunc.algEquivOfTranscendental z hz).injective hpq)
  have hGz : (G.map (mapRingHom (algebraMap K (IntermediateField.adjoin K ({z} : Set F))))).map
      (evalRingHom zz) = G.map φ := Polynomial.map_map _ _ _
  have hφF : (algebraMap (IntermediateField.adjoin K ({z} : Set F)) F).comp φ
      = (evalRingHom z).comp (mapRingHom (algebraMap K F)) := by
    refine Polynomial.ringHom_ext (fun k => ?_) ?_
    · simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, Polynomial.map_C, eval_C]
      rw [hφapply, aeval_C]
      exact (IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({z} : Set F)) F k).symm
    · simp only [RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom, Polynomial.map_X, eval_X]
      rw [hφapply, aeval_X]
      exact hzzF
  have hroot : aeval y (G.map φ) = 0 := by
    rw [aeval_def, eval₂_map, hφF, ← eval_map, ← Polynomial.map_map, map_evalRingHom_eval]
    exact hG
  have hdeg : G.natDegree ≠ 0 := by
    intro h0
    have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have h1 : algebraMap (IntermediateField.adjoin K ({z} : Set F)) F (φ (G.coeff 0)) = 0 := by
      rw [← hroot, hGC, Polynomial.map_C, aeval_C, coeff_C_zero]
    have h2 : φ (G.coeff 0) = 0 := by
      rwa [map_eq_zero_iff _ (algebraMap (IntermediateField.adjoin K ({z} : Set F)) F).injective]
        at h1
    have hc : G.coeff 0 = 0 := hφinj (by rw [h2, map_zero])
    exact hGirr.ne_zero (by rw [hGC, hc, map_zero])
  have hprim : G.IsPrimitive := hGirr.isPrimitive hdeg
  have hirrQ : Irreducible (G.map (algebraMap K[X] (RatFunc K))) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mp hGirr
  have hmapψ : Polynomial.mapEquiv (RatFunc.algEquivOfTranscendental z hz).toRingEquiv
      (G.map (algebraMap K[X] (RatFunc K))) = G.map φ := by
    rw [mapEquiv_apply, Polynomial.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, ← hψ p]
    rfl
  have hirr : Irreducible (G.map φ) := by
    rw [← hmapψ]
    exact (MulEquiv.irreducible_iff _).mpr hirrQ
  have hmin := minpoly.eq_of_irreducible hirr hroot
  have hlc : (G.map φ).leadingCoeff = φ G.leadingCoeff := leadingCoeff_map_of_injective hφinj G
  have hlc0 : (G.map φ).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hGz_eq : G.map φ = C (φ G.leadingCoeff) * minpoly (IntermediateField.adjoin K ({z} : Set F))
    y := by
    rw [← hmin, ← hlc, mul_comm (G.map φ), ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc0, C_1, one_mul]
  rw [hGz, hGz_eq, eval_mul, eval_C]
  rfl

end AlgebraicCurve.Place

open _root_.AlgebraicCurve.Place AlgebraicCurve.Place in
theorem _root_.AlgebraicCurve.Place.eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (hrat : ∀ w : Place K F, w.IsRational)
    {z y : F} (hz : Transcendental K z)
    (G : Polynomial (Polynomial K)) (hGirr : Irreducible G)
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (z₀ : K) (Q : Place K F) (hzQ : z ∈ Q.toValuationSubring) (hQ : Q.evalAt z = z₀)
    (hreg : ∀ w : Place K F, z ∈ w.toValuationSubring → w.evalAt z = z₀ → y ∈ w.toValuationSubring)
      :
    G.leadingCoeff.eval z₀ ≠ 0 := by
  intro hlead0
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({z} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x₀ hz
  have hcz : CharZero (IntermediateField.adjoin K ({z} : Set F)) :=
    charZero_of_injective_algebraMap (algebraMap K (IntermediateField.adjoin K ({z} : Set
      F))).injective
  have hsepF : Algebra.IsSeparable (IntermediateField.adjoin K ({z} : Set F)) F :=
    Algebra.IsSeparable.of_integral _ _
  have hpd : HasPrincipalDivisors K F := hasPrincipalDivisors_of_transcendental K z hz
  let L : IntermediateField K F := IntermediateField.adjoin K ({z} : Set F)
  let zz : L := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  have hzcoe : algebraMap L F zz = z := rfl
  have hv : Q.IsRational := hrat Q
  have hinjz : Function.Injective (aeval z : K[X] →ₐ[K] F) := transcendental_iff_injective.mp hz
  set v : Place K L := Q.restrict L with hvdef
  have hzzv : zz ∈ v.toValuationSubring := by
    rw [hvdef]
    exact (Q.mem_restrict_iff (f := zz)).mpr hzQ
  have hpush : ∀ p : K[X],
      algebraMap L F ((p.map (algebraMap K L)).eval zz) = (p.map (algebraMap K F)).eval z := by
    intro p
    rw [eval_map, hom_eval₂, ← IsScalarTower.algebraMap_eq, ← eval_map]
    rfl
  have hdeg : G.natDegree ≠ 0 := by
    intro h0
    have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have h1 : aeval z (G.coeff 0) = 0 := by
      have h2 := hG
      rw [hGC, Polynomial.map_C, evalEval_C, coe_mapRingHom, eval_map, ← aeval_def] at h2
      exact h2
    have hc0 : G.coeff 0 = 0 := hinjz (by simpa using h1)
    exact hGirr.ne_zero (by rw [hGC, hc0, map_zero])
  have hQpos : 0 < Q.ord (z - algebraMap K F z₀) := by
    refine Q.rfg_ord_sub_algebraMap_pos hv hzQ hQ ?_
    intro h
    exact hz (by rw [h]; exact isAlgebraic_algebraMap z₀)
  have ht : algebraMap L F (zz - algebraMap K L z₀) = z - algebraMap K F z₀ := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, hzcoe]
  have hvpos : 0 < v.ord (zz - algebraMap K L z₀) := by
    have h2 := Q.ord_restrict (zz - algebraMap K L z₀)
    rw [ht, ← hvdef] at h2
    have heQ : (0 : ℤ) ≤ (Q.ramificationIndex L : ℤ) := by exact_mod_cast (Nat.zero_le _)
    rcases lt_or_ge 0 (v.ord (zz - algebraMap K L z₀)) with hpos | hle
    · exact hpos
    · exfalso
      have : (Q.ramificationIndex L : ℤ) * v.ord (zz - algebraMap K L z₀) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inl ⟨heQ, hle⟩)
      omega
  have hfib : ∀ w : Place K F, w.restrict L = v → z ∈ w.toValuationSubring ∧ w.evalAt z = z₀ := by
    intro w hw
    have hzw' : zz ∈ (w.restrict L).toValuationSubring := by rw [hw]; exact hzzv
    have hzw : z ∈ w.toValuationSubring := (w.mem_restrict_iff (f := zz)).mp hzw'
    refine ⟨hzw, ?_⟩
    by_contra hne
    have h0 := w.rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne (hrat w) hzw hne
    have h1 := w.ord_restrict (zz - algebraMap K L z₀)
    rw [ht, hw] at h1
    have hew : (0 : ℤ) < (w.ramificationIndex L : ℤ) :=
      by exact_mod_cast w.ramificationIndex_pos (F := L)
    have : 0 < w.ord (z - algebraMap K F z₀) := by rw [h1]; exact mul_pos hew hvpos
    omega
  have hint : IsIntegral v.toValuationSubring y := by
    by_cases hy0 : y = 0
    · rw [hy0]; exact isIntegral_zero
    have hord : ∀ w ∈ v.fiber F, 0 ≤ w.ord y := by
      intro w hw
      obtain ⟨hzw, hwz⟩ := hfib w (mem_fiber.mp hw)
      exact w.ord_nonneg_of_mem (hreg w hzw hwz)
    obtain ⟨c, hc⟩ := exists_integralClosureAt_of_ord_fiber_nonneg (v := v) hy0 hord
    rw [← hc]
    exact c.2
  have hminO : minpoly L y
      = (minpoly v.toValuationSubring y).map (algebraMap v.toValuationSubring L) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (K := L) hint
  have hS4 : ∀ c : L, ((G.map (mapRingHom (algebraMap K L))).map (evalRingHom zz)).eval c
      = ((G.leadingCoeff).map (algebraMap K L)).eval zz * (minpoly L y).eval c :=
    fun c => rf_gauss_minpoly hz y G hGirr hG c
  have hGz : (G.map (mapRingHom (algebraMap K L))).map (evalRingHom zz)
      = C (((G.leadingCoeff).map (algebraMap K L)).eval zz) * minpoly L y :=
    Polynomial.funext (fun c => by rw [hS4 c, eval_mul, eval_C])
  have hcoef : ∀ i, ((G.coeff i).map (algebraMap K L)).eval zz
      = ((G.leadingCoeff).map (algebraMap K L)).eval zz
          * algebraMap v.toValuationSubring L ((minpoly v.toValuationSubring y).coeff i) := by
    intro i
    have h := congrArg (fun p => Polynomial.coeff p i) hGz
    simp only [coeff_map, coe_evalRingHom, coe_mapRingHom, coeff_C_mul] at h
    rw [hminO, coeff_map] at h
    exact h
  have key : ∀ i, ∃ b : F, b ∈ Q.toValuationSubring ∧
      ((G.coeff i).map (algebraMap K F)).eval z = ((G.leadingCoeff).map (algebraMap K F)).eval z *
        b := by
    intro i
    refine ⟨algebraMap L F (algebraMap v.toValuationSubring L ((minpoly v.toValuationSubring
      y).coeff i)),
      ?_, ?_⟩
    · exact (Q.mem_restrict_iff (f := _)).mp ((minpoly v.toValuationSubring y).coeff i).2
    · have h := congrArg (algebraMap L F) (hcoef i)
      rw [map_mul, hpush, hpush] at h
      exact h
  have haz : ((G.leadingCoeff).map (algebraMap K F)).eval z ≠ 0 := by
    rw [Ne, eval_map, ← aeval_def]
    exact fun h => (leadingCoeff_ne_zero.mpr hGirr.ne_zero) (hinjz (by simpa using h))
  have hordA : 0 < Q.ord (((G.leadingCoeff).map (algebraMap K F)).eval z) := by
    have hmem := Q.g2p_eval_mem G.leadingCoeff hzQ
    have hval : Q.evalAt (((G.leadingCoeff).map (algebraMap K F)).eval z) = 0 := by
      rw [Q.g2p_evalAt_eval hv _ hzQ, hQ]
      exact hlead0
    have h := Q.rfg_ord_sub_algebraMap_pos hv hmem hval (by rw [map_zero]; exact haz)
    rwa [map_zero, sub_zero] at h
  have hroot : ∀ i, (G.coeff i).IsRoot z₀ := by
    intro i
    by_cases hpi : G.coeff i = 0
    · simp [hpi]
    have hfz0 : ((G.coeff i).map (algebraMap K F)).eval z ≠ 0 := by
      rw [Ne, eval_map, ← aeval_def]
      exact fun h => hpi (hinjz (by simpa using h))
    obtain ⟨b, hbQ, hfac⟩ := key i
    have hb0 : b ≠ 0 := fun h => hfz0 (by rw [hfac, h, mul_zero])
    have hordf : 0 < Q.ord (((G.coeff i).map (algebraMap K F)).eval z) := by
      rw [hfac, Q.ord_mul haz hb0]
      have := Q.ord_nonneg_of_mem hbQ
      omega
    have hmemf := Q.g2p_eval_mem (G.coeff i) hzQ
    by_contra hne
    have hval : Q.evalAt (((G.coeff i).map (algebraMap K F)).eval z) ≠ 0 := by
      rw [Q.g2p_evalAt_eval hv _ hzQ, hQ]
      exact hne
    have h0 := Q.rfg_ord_sub_algebraMap_eq_zero_of_evalAt_ne hv hmemf hval
    rw [map_zero, sub_zero] at h0
    omega
  have hdvd : C (X - C z₀) ∣ G :=
    (C_dvd_iff_dvd_coeff _ _).mpr (fun i => dvd_iff_isRoot.mpr (hroot i))
  obtain ⟨H, hH⟩ := hdvd
  rcases hGirr.isUnit_or_isUnit hH with hu | hu
  · have hu' : IsUnit (X - C z₀) := isUnit_C.mp hu
    have := natDegree_eq_zero_of_isUnit hu'
    rw [natDegree_X_sub_C] at this
    exact one_ne_zero this
  · apply hdeg
    rw [hH, natDegree_mul (C_ne_zero.mpr (X_sub_C_ne_zero z₀)) hu.ne_zero, natDegree_C,
      natDegree_eq_zero_of_isUnit hu]

end AlgebraicCurves.Places.Proofs.Place_eval_leadingCoeff_ne_zero_of_forall_mem_toValuationSubring
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

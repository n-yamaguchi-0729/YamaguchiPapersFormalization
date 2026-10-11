/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Taylor
import AlgebraicCurves.Places.EvaluationAlgebra
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Places.Place_evalEval_C_add_X_mk_taylorCoeff_eq_zero
import AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_hensel_lift_unique
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Place eq map mk taylor Coeff of eval Eval C add X eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero

open AlgebraicCurve AlgebraicCurve.Place Polynomial

namespace ProofAuxG2
open AlgebraicCurve AlgebraicCurve.Place Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem taylorRem_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorRem v t 0 r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [taylorRem_succ, ih, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq, map_zero,
      sub_self, zero_mul]

theorem taylorCoeff_zero_fun (v : Place K F) (t : F) (r : ℕ) : taylorCoeff v t r 0 = 0 := by
  rw [taylorCoeff_eq, taylorRem_zero_fun, ← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]

theorem taylorRem_algebraMap_one (v : Place K F) (t : F) (c : K) :
    taylorRem v t (algebraMap K F c) 1 = 0 := by
  change (taylorRem v t (algebraMap K F c) 0 - _) * t⁻¹ = 0
  rw [taylorRem_zero, v.evalAt_algebraMap_eq, sub_self, zero_mul]

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {g : F} (hg0 : g ≠ 0) (hpos : 0 < v.ord g) :
    v.evalAt g = 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hg0 hpos.le
  have hnu : ¬ IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    simp only [IsUnit.unit_spec] at this
    change v.ord g = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (by simpa [mem_nonunits_iff] using hnu)
  rw [v.evalAt_of_mem hmem, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

end ProofAuxG2

open ProofAuxG2 in
theorem _root_.AlgebraicCurve.Place.eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] {L : Type*} [Field L] (ι : K →+* L)
    (v : Place K F) (hv : v.IsRational) {z y : F}
    (hz : z ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring)
    (ht : v.ord (z - algebraMap K F (v.evalAt z)) = 1)
    (G : Polynomial (Polynomial K))
    (hG : (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0)
    (hsep : (Polynomial.derivative G).evalEval (v.evalAt z) (v.evalAt y) ≠ 0)
    (Y : PowerSeries L) (hY0 : PowerSeries.constantCoeff Y = ι (v.evalAt y))
    (hY : (G.map (Polynomial.mapRingHom (PowerSeries.C.comp ι))).evalEval
        (PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X) Y = 0) :
    Y = PowerSeries.map ι
          (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) := by
  set a : PowerSeries L := PowerSeries.map ι
    (PowerSeries.mk fun n => taylorCoeff v (z - algebraMap K F (v.evalAt z)) n y) with ha
  set x : PowerSeries L := PowerSeries.C (ι (v.evalAt z)) + PowerSeries.X with hx
  set p : Polynomial (Polynomial (PowerSeries L)) := G.map (Polynomial.mapRingHom
    (PowerSeries.C.comp ι))
    with hp
  set f : Polynomial (PowerSeries L) := p.map (Polynomial.evalRingHom x) with hf
  have hfeval : ∀ b, f.eval b = p.evalEval x b := fun b => Polynomial.map_evalRingHom_eval x b p
  have hK := evalEval_C_add_X_mk_taylorCoeff_eq_zero v hv hz hy ht G hG
  have ha_root : f.IsRoot a := by
    rw [Polynomial.IsRoot, hfeval]
    have := congrArg (PowerSeries.map ι) hK
    rw [map_zero, ← Polynomial.map_mapRingHom_evalEval, Polynomial.map_map,
      Polynomial.mapRingHom_comp]
      at this
    have hcomp : (PowerSeries.map ι).comp (algebraMap K (PowerSeries K)) = PowerSeries.C.comp ι :=
      by
      refine RingHom.ext fun c => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, ← PowerSeries.C_eq_algebraMap, PowerSeries.map_C]
    rw [hcomp, map_add, PowerSeries.map_C, PowerSeries.map_X] at this
    exact this
  have hb_root : f.IsRoot Y := by rw [Polynomial.IsRoot, hfeval]; exact hY
  have ha0 : PowerSeries.constantCoeff a = ι (v.evalAt y) := by
    rw [ha, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_mk, taylorCoeff_zero]
  have hmem : Y - a ∈ IsLocalRing.maximalIdeal (PowerSeries L) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker, map_sub, hY0, ha0, sub_self]
  have hunit : IsUnit (f.derivative.eval a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    rw [hf, Polynomial.derivative_map, Polynomial.map_evalRingHom_eval, hp,
      Polynomial.derivative_map,
      ← Polynomial.map_mapRingHom_evalEval PowerSeries.constantCoeff, Polynomial.map_map,
      Polynomial.mapRingHom_comp]
    have hcc : PowerSeries.constantCoeff.comp (PowerSeries.C.comp ι) = ι := by
      refine RingHom.ext fun c => ?_
      simp [PowerSeries.constantCoeff_C]
    rw [hcc, hx, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero, ha0,
      Polynomial.map_mapRingHom_evalEval ι, _root_.map_ne_zero ι]
    exact hsep
  exact (IsLocalRing.hensel_lift_unique ha_root hb_root hmem hunit).symm
end AlgebraicCurves.Places.Proofs.Place_eq_map_mk_taylorCoeff_of_evalEval_C_add_X_eq_zero
end ProofImplementation

open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe

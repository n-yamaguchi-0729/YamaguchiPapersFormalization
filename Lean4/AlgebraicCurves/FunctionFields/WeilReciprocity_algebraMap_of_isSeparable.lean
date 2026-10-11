/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_weilReciprocity_algebraMap_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.OverDVR
import AlgebraicCurves.Divisors.Divisor_pushforward_div_of_isSeparable
import AlgebraicCurves.Places.Place_ord_norm_eq_zero_of_forall_fiber_of_isSeparable
import AlgebraicCurves.Divisors.Divisor_evalFun_pullback
import AlgebraicCurves.Divisors.Divisor_evalFun_algebraMap_pushforward

/-!
# Weil Reciprocity algebra Map of is Separable
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.WeilReciprocity_algebraMap_of_isSeparable
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

theorem _root_.AlgebraicCurve.weilReciprocity_algebraMap_of_isSeparable {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F]
  [HasPrincipalDivisors K F'] (hbase : WeilReciprocity K F) {f : F'} {g : F} (hf : f ≠ 0) (hg : g ≠
  0) (Df Dg : Divisor K F') (hDf : ∀ w : Place K F', Df w = w.ord f) (hDg : ∀ w : Place K F', Dg w
  = w.ord (algebraMap F F' g)) (hdisj : ∀ w : Place K F', w.ord f = 0 ∨ w.ord (algebraMap F F' g) =
  0) (hratf : ∀ w ∈ Df.support, Place.IsRational w) (hratF : ∀ v : Place K F, v.IsRational)
  (hratfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', Place.IsRational w) : Divisor.evalFun
  f Dg = Divisor.evalFun (algebraMap F F' g) Df := by
  classical
  have hNf : Algebra.norm F f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  obtain ⟨Eg, hEg, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  obtain ⟨EN, hEN, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (Algebra.norm F f) hNf
  have hfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', w.ord f = 0 := by
    intro v hv w hw
    refine (hdisj w).resolve_right ?_
    rw [w.ord_restrict (F := F) g, Place.mem_fiber.mp hw]
    have hepos := w.ramificationIndex_pos (F := F)
    exact mul_ne_zero (by exact_mod_cast hepos.ne') hv
  have hres : ∀ w : Place K F', w.ord f ≠ 0 → (w.restrict F).ord g = 0 := by
    intro w hw
    have hzero := (hdisj w).resolve_left hw
    rw [w.ord_restrict (F := F) g] at hzero
    have hepos := w.ramificationIndex_pos (F := F)
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (by exact_mod_cast hepos.ne')
    · exact h
  have hdisjF : ∀ v : Place K F, v.ord (Algebra.norm F f) = 0 ∨ v.ord g = 0 := by
    intro v
    rcases eq_or_ne (v.ord g) 0 with h | h
    · exact Or.inr h
    · exact Or.inl (AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber_of_isSeparable hf v (hfib
        v h))
  have hstep1 : Dg = Divisor.pullback F' Eg := by
    ext w
    rw [hDg w, Divisor.pullback_apply_eq_ord (fun u => hEg u)]
  have hstep4 : Divisor.pushforward F Df = EN :=
    AlgebraicCurve.Divisor.pushforward_div_of_isSeparable hf hDf hEN
  have hstep2 : Divisor.evalFun f (Divisor.pullback F' Eg)
      = Divisor.evalFun (Algebra.norm F f) Eg := by
    refine AlgebraicCurve.Divisor.evalFun_pullback hf Eg (fun v _ => hratF v) (fun v hv w hw => ?_)
      (fun v hv w hw => ?_)
    · exact hratfib v (by rw [← hEg v]; exact Finsupp.mem_support_iff.mp hv) w hw
    · exact hfib v (by rw [← hEg v]; exact Finsupp.mem_support_iff.mp hv) w hw
  have hstep3 : Divisor.evalFun (Algebra.norm F f) Eg = Divisor.evalFun g EN :=
    hbase (Algebra.norm F f) g EN Eg hNf hg hEN hEg hdisjF
      (fun v _ => hratF v) (fun v _ => hratF v)
  have hstep5 : Divisor.evalFun (algebraMap F F' g) Df
      = Divisor.evalFun g (Divisor.pushforward F Df) := by
    refine AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward hg Df (fun w hw => hratf w hw)
      (fun w _ => hratF _) (fun w hw => ?_)
    exact hres w (by rw [← hDf w]; exact Finsupp.mem_support_iff.mp hw)
  rw [hstep1, hstep2, hstep3, ← hstep4, ← hstep5]
end AlgebraicCurves.FunctionFields.Proofs.WeilReciprocity_algebraMap_of_isSeparable
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.Cech.DivisorSections
import AlgebraicCurves.Cohomology.RiemannRoch.Exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
import AlgebraicCurves.Places.Place_exists_forall_adicValuation_sub_eq

/-!
Find a divisor-bounded chart section realizing the prescribed valuation at a genus-reaching place.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs
namespace Exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt) in
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open WithZero

theorem exists_mem_lSpaceOn_adicValuation_eq' {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F) (v : Place K F) (hv :
      v ∈ S) :
    ∃ f : F, f ∈ lSpaceOn S D ∧ v.adicValuation f = exp (D v) := by
  classical
  obtain ⟨a, ha⟩ := Place.exists_forall_adicValuation_sub_eq ({v} : Finset (Place K F)) (fun _ =>
    (0 : F)) (fun _ => D v)
  have hav : v.adicValuation a = exp (D v) := by
    have := ha v (Finset.mem_singleton_self v)
    rwa [sub_zero] at this
  let α : Place K F → F := fun w => if w = v then a else 0
  let E : Divisor K F := D - Finsupp.single v 1
  have hα : {w | w ∈ S ∧ ¬ w.adicValuation (α w) ≤ exp (E w)}.Finite := by
    apply (Set.finite_singleton v).subset
    rintro w ⟨-, hw⟩
    by_contra hwv
    apply hw
    have hαw : α w = 0 := ite_eq_right hwv
    rw [hαw, Valuation.map_zero]
    exact zero_le
  obtain ⟨f, hf⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt h S hv₀ E α hα
  have hEv : E v = D v - 1 := by simp [E]
  have hEw : ∀ w, w ≠ v → E w = D w := fun w hw => by
    rw [show E w = D w - Finsupp.single v (1 : ℤ) w from rfl, Finsupp.single_apply, ite_eq_right
      (fun h => hw h.symm),
      sub_zero]
  have hfv : v.adicValuation (a - f) < v.adicValuation a := by
    have := hf v hv
    simp only [α, ite_eq_left rfl, hEv] at this
    rw [hav]
    exact lt_of_le_of_lt this (exp_lt_exp.mpr (by omega))
  have hfval : v.adicValuation f = exp (D v) := by
    rw [← hav, show f = a - (a - f) by ring]
    exact Valuation.map_sub_eq_of_lt_left _ hfv
  refine ⟨f, ?_, hfval⟩
  intro w hwS
  by_cases hwv : w = v
  · subst hwv
    exact hfval.le
  · have := hf w hwS
    simp only [α, ite_eq_right hwv, hEw w hwv, zero_sub, Valuation.map_neg] at this
    exact this

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs in
open _root_.AlgebraicCurve
  Exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt.AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F} (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (S : Set (AlgebraicCurve.Place K F)) {v₀ : AlgebraicCurve.Place K F} (hv₀ : v₀ ∉ S)
    (D : AlgebraicCurve.Divisor K F) (v : AlgebraicCurve.Place K F) (hv : v ∈ S) :
    ∃ f : F, f ∈ AlgebraicCurve.lSpaceOn S D ∧ v.adicValuation f = WithZero.exp (D v) :=
  exists_mem_lSpaceOn_adicValuation_eq' h S hv₀ D v hv
end Exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs
end ProofImplementation

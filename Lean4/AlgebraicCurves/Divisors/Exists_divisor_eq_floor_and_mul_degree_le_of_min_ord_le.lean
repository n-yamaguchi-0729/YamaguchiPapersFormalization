/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.FunctionFields.IsCurveOver_of_isAlgClosed_of_transcendental
import AlgebraicCurves.Places.Exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed

/-!
# Exists divisor eq floor and mul degree le of min ord le
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve
open scoped IntermediateField

namespace DegEBody

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem degree_eq_sum_support (hdeg1 : ∀ v : Place k F, v.deg = 1) (D : Divisor k F) :
    D.degree = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun v _ =>
    by rw [AddMonoidHom.mulRight_apply, hdeg1 v, Nat.cast_one, mul_one]

end DegEBody

open DegEBody in
theorem _root_.AlgebraicCurve.exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (f : F) (hf : f ≠ 0)
    (m d : ℕ) (hd : 0 < d) :
    ∃ E : Divisor k F,
      (∀ v : Place k F, E v = ((m : ℤ) * (v.ord f - min 0 (v.ord x))) / (d : ℤ)) ∧
      (d : ℤ) * E.degree ≤ (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F :
        ℤ) := by
  classical
  have := hfin
  have : IsCurveOver k F := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hdeg1 : ∀ v : Place k F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := F) f hf
  obtain ⟨S, hS, hSsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed k x
    hx hfin
  set g : Place k F → ℤ := fun v => ((m : ℤ) * (v.ord f - min 0 (v.ord x))) / (d : ℤ) with hg
  set T : Finset (Place k F) := Df.support ∪ S with hT
  have hzero : ∀ v, v ∉ T → v.ord f = 0 ∧ 0 ≤ v.ord x := by
    intro v hv
    rw [hT, Finset.mem_union, not_or, Finsupp.mem_support_iff, not_not, hS, not_lt] at hv
    exact ⟨by rw [← hDf v]; exact hv.1, hv.2⟩
  have hgT : ∀ v, g v ≠ 0 → v ∈ T := by
    intro v hv
    by_contra hvT
    obtain ⟨h1, h2⟩ := hzero v hvT
    apply hv
    simp only [hg, h1, min_eq_left h2, sub_zero, mul_zero, Int.zero_ediv]
  let E : Divisor k F := Finsupp.onFinset T g (fun v hv => hgT v hv)
  have hE : ∀ v, E v = g v := fun v => Finsupp.onFinset_apply
  refine ⟨E, fun v => hE v, ?_⟩
  have hdegE : E.degree = ∑ v ∈ T, g v := by
    rw [degree_eq_sum_support hdeg1]
    rw [Finset.sum_congr rfl (fun v (_ : v ∈ E.support) => hE v)]
    exact Finset.sum_subset Finsupp.support_onFinset_subset (fun v _ hv => by
      rw [Finsupp.mem_support_iff, not_not] at hv
      exact (hE v).symm.trans hv)
  have hpt : ∀ v, (d : ℤ) * g v ≤ (m : ℤ) * (v.ord f - min 0 (v.ord x)) := fun v => by
    rw [hg, mul_comm]
    exact Int.ediv_mul_le _ (by exact_mod_cast hd.ne')
  have hsumf : ∑ v ∈ T, v.ord f = 0 := by
    have h1 : ∑ v ∈ Df.support, v.ord f = ∑ v ∈ T, v.ord f :=
      Finset.sum_subset Finset.subset_union_left (fun v _ hv => by
        rw [Finsupp.mem_support_iff, not_not] at hv
        rw [← hDf, hv])
    have h2 : Df.degree = ∑ v ∈ Df.support, v.ord f := by
      rw [degree_eq_sum_support hdeg1]
      exact Finset.sum_congr rfl fun v _ => hDf v
    rw [← h1, ← h2, hDf0]
  have hsumx : ∑ v ∈ T, (-min 0 (v.ord x)) =
      (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
    rw [← hSsum]
    have h1 : ∀ v ∈ S, -v.ord x = -min 0 (v.ord x) := fun v hv => by
      rw [min_eq_right ((hS v).mp hv).le]
    rw [Finset.sum_congr rfl h1]
    symm
    exact Finset.sum_subset Finset.subset_union_right (fun v _ hv => by
      rw [hS, not_lt] at hv
      rw [min_eq_left hv, neg_zero])
  calc (d : ℤ) * E.degree = ∑ v ∈ T, (d : ℤ) * g v := by rw [hdegE, Finset.mul_sum]
    _ ≤ ∑ v ∈ T, (m : ℤ) * (v.ord f - min 0 (v.ord x)) := Finset.sum_le_sum fun v _ => hpt v
    _ = (m : ℤ) * (∑ v ∈ T, v.ord f + ∑ v ∈ T, (-min 0 (v.ord x))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ = (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
        rw [hsumf, hsumx, zero_add]
end AlgebraicCurves.Divisors.Proofs.Exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
end ProofImplementation

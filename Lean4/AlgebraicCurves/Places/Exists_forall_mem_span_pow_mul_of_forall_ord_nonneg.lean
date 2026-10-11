/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.LSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
import AlgebraicCurves.FunctionFields.Exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace
import AlgebraicCurves.FunctionFields.IsCurveOver_of_isAlgClosed_of_transcendental

/-!
# Exists forall mem span pow mul of forall ord nonneg
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
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
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

open AlgebraicCurve

noncomputable section

theorem fd_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) := by
  have : IsCurveOver K F :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hell0 : ell (0 : Divisor K F) = 1 :=
    (AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD).1
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) hell0
  exact fun M => AlgebraicCurve.finiteDimensional_lSpace (M • D)

theorem exists_mem_lSpace_nsmul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (h : F) (hh : ∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) :
    ∃ M : ℕ, h ∈ LSpace (M • D) := by
  rcases eq_or_ne h 0 with rfl | hh0
  · exact ⟨0, (LSpace _).zero_mem⟩
  refine ⟨D.support.sup (fun v => (-(v.ord h)).toNat), mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)⟩
  set M := D.support.sup (fun v => (-(v.ord h)).toNat) with hM
  simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul, neg_le]
  by_cases hv : v ∈ D.support
  · have hDv1 : (1:ℤ) ≤ D v := by
      have hne := Finsupp.mem_support_iff.mp hv
      have := hD v; omega
    have hMv : ((-(v.ord h)).toNat : ℤ) ≤ (M : ℤ) := by
      have h' := Finset.le_sup (f := fun w => (-(w.ord h)).toNat) hv
      exact_mod_cast h'
    calc -(v.ord h) ≤ ((-(v.ord h)).toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (M : ℤ) := hMv
      _ = (M : ℤ) * 1 := (mul_one _).symm
      _ ≤ (M : ℤ) * D v := mul_le_mul_of_nonneg_left hDv1 (Nat.cast_nonneg M)
  · have hDv0 : D v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hDv0, mul_zero]
    have hox : 0 ≤ v.ord x := by
      have := hD v; rw [hDv0] at this; omega
    exact neg_nonpos_of_nonneg (hh v hox)

theorem _root_.AlgebraicCurve.exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∃ M₁ : ℕ, ∀ h : F, (∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) →
      h ∈ Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} := by
  classical
  obtain ⟨_, M₀, hM₀1, hell⟩ :=
    AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD
  have hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) :=
    fd_lSpace_nsmul_poleDivisor x hx D hD
  set M₁ := M₀ + 1
  refine ⟨M₁, fun h hh => ?_⟩
  set SP := Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} with hSP
  have hD0 : (0 : Divisor K F) ≤ D := fun v => by rw [hD]; exact le_max_left _ _
  have hbase : (LSpace (M₁ • D) : Submodule K F) ≤ SP := fun y hy =>
    Submodule.subset_span ⟨0, y, hy, by rw [pow_zero, one_mul]⟩
  have hxSP : (SP.map (LinearMap.mulLeft K x) : Submodule K F) ≤ SP := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, y, hy, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨j+1, y, hy, ?_⟩
    rw [LinearMap.mulLeft_apply]; ring
  have hup : ∀ k, (LSpace ((M₁ + k) • D) : Submodule K F) ≤ SP := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ n ih =>
      have hdegD : (0:ℤ) ≤ Divisor.degree D := by
        simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight,
          Finsupp.sum]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using hD0 v) (Nat.cast_nonneg _)
      have hstep := AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
        x D hD hFD M₀ (Divisor.degree D).toNat (genusFF K F)
        (fun N hN => by rw [hell N hN, Int.toNat_of_nonneg hdegD])
        (M₁ + n) (by omega)
      refine hstep.trans (sup_le ih ?_)
      exact (Submodule.map_mono ih).trans hxSP
  have hall : ∀ m, (LSpace (m • D) : Submodule K F) ≤ SP := fun m => by
    refine (lSpace_mono ?_).trans (hup m)
    intro v
    have hDv : (0:ℤ) ≤ D v := by simpa using hD0 v
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    have hmle : (m : ℤ) ≤ ((M₁+m:ℕ):ℤ) := by exact_mod_cast Nat.le_add_left m M₁
    exact mul_le_mul_of_nonneg_right hmle hDv
  obtain ⟨M, hMmem⟩ := exists_mem_lSpace_nsmul_of_forall_ord_nonneg x D hD h hh
  exact hall M hMmem
end
end AlgebraicCurves.Places.Proofs.Exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
end ProofImplementation

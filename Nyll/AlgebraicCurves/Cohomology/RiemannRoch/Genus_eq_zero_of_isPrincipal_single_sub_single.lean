/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Differentials.Uniformizer
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.FunctionFields.LinearIndependent_pow_of_transcendental
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Ell_eq_zero_of_degree_neg
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Degree_canonicalDivisor_eq_of_riemannRoch
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase

/-!
# Genus eq zero of is Principal single sub single
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusZeroPrincipalSingleSub
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve hiding Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg
  Place.mem_iff_ord_nonneg
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place hiding ord_nonneg_of_mem mem_of_ord_nonneg mem_iff_ord_nonneg
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve hiding Place.ord_nonneg_of_mem Place.mem_of_ord_nonneg
  Place.mem_iff_ord_nonneg

theorem genus_eq_zero_of_isPrincipal_single_sub_single_port {K : Type*} {F : Type*} [Field K]
  [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 := by
  classical
  obtain ⟨f, hf0, hdiv⟩ := h
  have hordQ : Q.ord f = -1 := by
    have := hdiv Q
    rw [Finsupp.sub_apply, Finsupp.single_apply, ite_eq_right hPQ, Finsupp.single_eq_same] at this
    linarith [this]
  have hordv : ∀ v : Place K F, v ≠ Q → 0 ≤ v.ord f := by
    intro v hv
    have := hdiv v
    rw [← this, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, ite_eq_right
      (Ne.symm hv)]
    by_cases hvP : P = v
    · rw [ite_eq_left hvP]; norm_num
    · rw [ite_eq_right hvP]; norm_num
  have : Nonempty (Place K F) := ⟨Q⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  have : Nontrivial Ω[F⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2
  have hftr : Transcendental K f := by
    intro halg
    have hint : IsIntegral K f := halg.isIntegral
    have hmem : f ∈ Q.toValuationSubring := by
      have hint' : IsIntegral Q.toValuationSubring f := hint.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Q.toValuationSubring) (K :=
        F)).mp hint'
      rw [← hy]; exact y.2
    have := Q.ord_nonneg_of_mem hmem
    linarith
  have hpow : ∀ n k : ℕ, k ≤ n → f ^ k ∈ LSpace ((n : ℤ) • Finsupp.single Q (1 : ℤ)) := by
    intro n k hk
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [← zpow_natCast, Place.ord_zpow]
    by_cases hv : v = Q
    · subst hv
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, hordQ]
      omega
    · have h0 : ((n : ℤ) • Finsupp.single Q (1 : ℤ)) v = 0 := by
        rw [Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hv), smul_zero]
      rw [h0, neg_zero]
      exact mul_nonneg (by positivity) (hordv v hv)
  have hell : ∀ n : ℕ, (n : ℤ) + 1 ≤ (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) := by
    intro n
    set D : Divisor K F := (n : ℤ) • Finsupp.single Q (1 : ℤ)
    have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
    let g : Fin (n + 1) → LSpace D := fun k => ⟨f ^ (k : ℕ), hpow n k (Nat.lt_succ_iff.mp k.2)⟩
    have hli : LinearIndependent K g := by
      have h1 : LinearIndependent K (fun k : Fin (n + 1) => f ^ (k : ℕ)) :=
        (linearIndependent_pow_of_transcendental hftr).comp (fun k : Fin (n+1) => (k : ℕ))
          (fun a b hab => Fin.ext hab)
      exact LinearIndependent.of_comp (LSpace D).subtype (by exact h1)
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    change (n : ℤ) + 1 ≤ (Module.finrank K (LSpace D) : ℤ)
    exact_mod_cast this
  obtain ⟨ω, hω⟩ : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  have hdegK := degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω
  have hdegD : Divisor.degree (((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ)) = ((2 * genus
    K F : ℕ) : ℤ) := by
    rw [map_zsmul, Divisor.degree_single, hQ]; simp
  have hRRD := hRR hω (((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ))
  have hzero : ell (canonicalDivisorOf hω - ((2 * genus K F : ℕ) : ℤ) • Finsupp.single Q (1 : ℤ))
    = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [map_sub, hdegK, hdegD]; push_cast; omega
  rw [hzero, hdegD] at hRRD
  have hlow := hell (2 * genus K F)
  push_cast at hlow hRRD ⊢
  omega

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs in
open _root_.AlgebraicCurve hiding
  Place.ord_nonneg_of_mem
  Place.mem_of_ord_nonneg
  Place.mem_iff_ord_nonneg in
open GenusZeroPrincipalSingleSub.AlgebraicCurve in
theorem _root_.AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single {K : Type*} {F :
  Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {P Q : Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genus K F = 0 :=
  AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single_port hRR hC hPQ hQ h
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusZeroPrincipalSingleSub
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero
attribute [-simp] AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

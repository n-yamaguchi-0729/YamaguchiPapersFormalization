/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ConstantExtension
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LSpace_pullbackConstants_eq_span_of_isConstantFieldExtension

/-!
# Divisor is Principal of is Principal pullback Constants of is Constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

namespace P2mConormPrincipalDescent

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  exact (w.adicValuation_le_one_iff.mp (w.adicValuation_le_one_of_mem hf)).resolve_left hf0

theorem ord_algebraMap (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 := ord_nonneg_of_mem w (w.algebraMap_mem' a)
  have h2 := ord_nonneg_of_mem w (w.algebraMap_mem' a⁻¹)
  rw [map_inv₀, w.ord_inv] at h2
  omega

theorem mem_range_of_isAlgebraic (hC : ConstantsAreBase k L) (y : L) (hy : IsAlgebraic k y) :
    y ∈ (algebraMap k L).range := by
  have hy' : y ∈ LSpace (0 : Divisor k L) := by
    intro v
    simp only [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    apply v.adicValuation_le_one_of_mem
    have hint : IsIntegral v.toValuationSubring y := hy.isIntegral.tower_top
    obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hx]
    exact x.2
  rw [show LSpace (0 : Divisor k L) = _ from hC] at hy'
  obtain ⟨c, hc⟩ := hy'
  exact ⟨c, hc⟩

theorem ord_eq_zero_of_mem_lSpace_zero (hC : ConstantsAreBase k L) {f : L}
    (hf : f ∈ LSpace (0 : Divisor k L)) (v : Place k L) : v.ord f = 0 := by
  rw [show LSpace (0 : Divisor k L) = _ from hC] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc]
  exact ord_algebraMap v c

end Basic

section Main

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [HasPrincipalDivisors K' F']

theorem exists_ne_zero_mem_lSpace
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (E : Divisor K F) (hE : (Divisor.pullbackConstants K' F' E).IsPrincipal) :
    ∃ x : F, x ≠ 0 ∧ x ∈ LSpace E := by
  obtain ⟨g, hg0, hg⟩ := hE
  have hmem : g⁻¹ ∈ LSpace (Divisor.pullbackConstants K' F' E) := by
    rw [mem_lSpace_iff_ord]
    right
    intro W
    rw [W.ord_inv, ← hg W]
  rw [AlgebraicCurve.lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension hgen hconst E]
    at hmem
  by_contra hne
  push Not at hne
  have hzero : (algebraMap F F' '' (LSpace E : Set F)) ⊆ ({0} : Set F') := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : x = 0 := by
      by_contra h
      exact hne x h hx
    simp [hx0]
  have h0 : g⁻¹ ∈ Submodule.span K' ({0} : Set F') := Submodule.span_mono hzero hmem
  rw [Submodule.span_zero_singleton, Submodule.mem_bot] at h0
  exact inv_ne_zero hg0 h0

theorem isPrincipal_of_isPrincipal_pullbackConstants
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hC : ConstantsAreBase K F)
    {D : Divisor K F} (hD : (Divisor.pullbackConstants K' F' D).IsPrincipal) :
    D.IsPrincipal := by
  have hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range :=
    mem_range_of_isAlgebraic hC
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lSpace hgen hconst D hD
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_mem_lSpace hgen hconst (-D)
    (by rw [map_neg]; exact (Divisor.principal (K := K') (F := F')).neg_mem hD)
  have hx' := (mem_lSpace_iff_ord.mp hx).resolve_left hx0
  have hy' := (mem_lSpace_iff_ord.mp hy).resolve_left hy0
  have hxy : x * y ∈ LSpace (0 : Divisor K F) := by
    rw [mem_lSpace_iff_ord]
    right
    intro v
    have h1 := hx' v
    have h2 := hy' v
    rw [Finsupp.neg_apply, neg_neg] at h2
    rw [v.ord_mul hx0 hy0, Finsupp.coe_zero, Pi.zero_apply, neg_zero]
    linarith
  refine ⟨y, hy0, fun v => le_antisymm ?_ ?_⟩
  · have h2 := hy' v
    rwa [Finsupp.neg_apply, neg_neg] at h2
  · have h1 := hx' v
    have h0 := ord_eq_zero_of_mem_lSpace_zero hC hxy v
    rw [v.ord_mul hx0 hy0] at h0
    linarith

end Main

end P2mConormPrincipalDescent

end Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
end AlgebraicCurves.Divisors.Proofs

namespace AlgebraicCurve.Divisor



open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension in
open AlgebraicCurve in
open P2mConormPrincipalDescent in
theorem isPrincipal_of_isPrincipal_pullbackConstants_of_isConstantFieldExtension
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    [AlgebraicCurve.HasPrincipalDivisors K' F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hC : AlgebraicCurve.ConstantsAreBase K F)
    {D : AlgebraicCurve.Divisor K F}
    (hD : (AlgebraicCurve.Divisor.pullbackConstants K' F' D).IsPrincipal) :
    D.IsPrincipal :=
  isPrincipal_of_isPrincipal_pullbackConstants hgen hC hD
end AlgebraicCurve.Divisor
end ProofImplementation

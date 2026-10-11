/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_list_isPrincipal_sub_sum_single_sub_smul_single.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_canonicalDivisor_genus_riemannRoch
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.RROpens_exists_effective_sub_add_smul_single_mem_principal

/-!
# Exists list is Principal sub sum single sub smul single
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Exists_list_isPrincipal_sub_sum_single_sub_smul_single
open _root_.IsDedekindDomain.HeightOneSpectrum in
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

universe u v

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace FFRepGlue
open _root_.AlgebraicCurve

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]


theorem exists_list_sum_single_eq (hdeg : ∀ v : Place K F, v.deg = 1) :
    ∀ E : Divisor K F, 0 ≤ E →
      ∃ l : List (Place K F), (l.map fun v => Finsupp.single v (1 : ℤ)).sum = E ∧ (l.length : ℤ) =
        Divisor.degree E := by
  classical
  intro E
  induction E using Finsupp.induction with
  | zero => intro _; exact ⟨[], by simp, by simp⟩
  | single_add v n E hv hn ih =>
      intro hE
      have hEv : ∀ w, 0 ≤ (Finsupp.single v n + E) w := fun w => hE w
      have hn0 : 0 ≤ n := by
        have := hEv v
        rw [Finsupp.add_apply, Finsupp.single_eq_same] at this
        have hEv0 : E v = 0 := by simpa [Finsupp.mem_support_iff] using hv
        omega
      have hE' : 0 ≤ E := by
        intro w
        rcases eq_or_ne w v with rfl | hw
        · have hEv0 : E w = 0 := by simpa [Finsupp.mem_support_iff] using hv
          simp [hEv0]
        · have := hEv w
          have hs : (Finsupp.single v n) w = 0 := Finsupp.single_eq_of_ne hw
          rw [Finsupp.add_apply, hs, zero_add] at this
          simpa using this
      obtain ⟨l, hl, hlen⟩ := ih hE'
      refine ⟨List.replicate n.toNat v ++ l, ?_, ?_⟩
      · rw [List.map_append, List.sum_append, hl, List.map_replicate, List.sum_replicate, ←
          Finsupp.smul_single_one v n]
        congr 1
        rw [← natCast_zsmul, Int.toNat_of_nonneg hn0]
      · rw [List.length_append, List.length_replicate, Nat.cast_add, hlen, map_add,
          Divisor.degree_single, hdeg, Nat.cast_one,
          mul_one, Int.toNat_of_nonneg hn0]

end AlgebraicCurve.FFRepGlue

open AlgebraicCurve.FFRepGlue in
theorem _root_.AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
    {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (v₀ : Place K F) (D : Divisor K F) (hD : Divisor.degree D = 0) :
    ∃ l : List (Place K F),
      Divisor.IsPrincipal
        (D - ((l.map fun v => Finsupp.single v (1 : ℤ)).sum - (l.length : ℤ) • Finsupp.single v₀
          1)) := by
  classical
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Kc, g, hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch K F
  obtain ⟨E, hE0, hE⟩ :=
    AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal g Kc hRR v₀ (hdeg1
      v₀) D hD
  obtain ⟨f, hf, hfE⟩ := (Divisor.mem_principal.mp hE)
  obtain ⟨Pf, hPf, hPfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  obtain ⟨l, hl, hlen⟩ := exists_list_sum_single_eq hdeg1 E (fun v => hE0 v)
  have hEeq : E = (D + (g : ℤ) • Finsupp.single v₀ 1) + Pf := by
    ext v
    have := hfE v
    rw [Finsupp.sub_apply] at this
    rw [Finsupp.add_apply, hPf v]
    linarith
  have hlen' : (l.length : ℤ) = g := by
    rw [hlen, hEeq, map_add, map_add, hD, hPfdeg, map_zsmul, Divisor.degree_single, hdeg1,
      Nat.cast_one, mul_one,
      smul_eq_mul, mul_one, zero_add, add_zero]
  refine ⟨l, f⁻¹, inv_ne_zero hf, fun v => ?_⟩
  rw [hl, hlen', Place.ord_inv, ← hfE v]
  simp only [Finsupp.sub_apply, Finsupp.add_apply]
  ring
end AlgebraicCurves.Divisors.Proofs.Exists_list_isPrincipal_sub_sum_single_sub_smul_single
end ProofImplementation

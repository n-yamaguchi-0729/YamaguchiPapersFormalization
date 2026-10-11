/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isCurveOver_and_essFiniteType_and_exists_of_adjoin_finset_eq_top_of_isAlgebraic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_perfectField

/-!
# Is Curve Over and ess Finite Type and exists of adjoin finset eq top of is Algebraic
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs
namespace IsCurveOver_and_essFiniteType_and_exists_of_adjoin_finset_eq_top_of_isAlgebraic
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

namespace IsCurveOfAlgGen

open IntermediateField

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_adjoin_t (S : Finset F) (hS : IntermediateField.adjoin K (S : Set F) = ⊤)
  (t : F)
    (halg : ∀ s ∈ S, IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) s) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  set L := IntermediateField.adjoin K ({t} : Set F)
  have : FiniteDimensional L (IntermediateField.adjoin L (S : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun s hs => (halg s (Finset.mem_coe.mp
      hs)).isIntegral
  have htop : IntermediateField.adjoin L (S : Set F) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin K (S : Set F) := by rw [hS]; trivial
    have hle : IntermediateField.adjoin K (S : Set F) ≤ (IntermediateField.adjoin L (S : Set
      F)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin L (S : Set F))
    exact hle hx
  have e : (⊤ : IntermediateField L F) ≃ₗ[L] F := (IntermediateField.topEquiv (F := L) (E :=
    F)).toLinearEquiv
  rw [← htop] at e
  exact LinearEquiv.finiteDimensional e

theorem essFiniteType (S : Finset F) (hS : IntermediateField.adjoin K (S : Set F) = ⊤) :
  Algebra.EssFiniteType K F := by
  set A : Subalgebra K F := Algebra.adjoin K (S : Set F) with hA
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset
    S)
  have : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  have : IsFractionRing A F := by
    apply IsFractionRing.of_field
    intro z
    have hz : z ∈ IntermediateField.adjoin K (S : Set F) := by rw [hS]; trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  have : Algebra.EssFiniteType K A := Algebra.EssFiniteType.of_finiteType K A
  have : Algebra.EssFiniteType A F := Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors A)
  exact Algebra.EssFiniteType.comp K A F

end IsCurveOfAlgGen

end IsCurveOver_and_essFiniteType_and_exists_of_adjoin_finset_eq_top_of_isAlgebraic
end AlgebraicCurves.FunctionFields.Proofs

namespace AlgebraicCurve



open _root_.AlgebraicCurves.FunctionFields.Proofs in
open IsCurveOver_and_essFiniteType_and_exists_of_adjoin_finset_eq_top_of_isAlgebraic in
open IsCurveOfAlgGen in
theorem isCurveOver_and_essFiniteType_and_exists_of_adjoin_finset_eq_top_of_isAlgebraic
    (K F : Type) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (S : Finset F) (hS : IntermediateField.adjoin K (S : Set F) = ⊤)
    (t : F) (ht : Transcendental K t)
    (halg : ∀ s ∈ S, IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) s) :
    AlgebraicCurve.IsCurveOver K F ∧ Algebra.EssFiniteType K F ∧
      (∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F))
        F) :=
  ⟨AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht (finiteDimensional_adjoin_t S hS
    t halg),
    essFiniteType S hS, t, ht, finiteDimensional_adjoin_t S hS t halg⟩
end AlgebraicCurve
end ProofImplementation

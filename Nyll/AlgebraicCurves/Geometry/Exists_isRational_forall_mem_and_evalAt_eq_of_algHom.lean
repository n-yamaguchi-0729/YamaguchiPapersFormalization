/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_isRational_forall_mem_and_evalAt_eq_of_algHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional
import Nyll.AlgebraicCurves.Places.Place_exists_of_valuationSubring_of_finiteDimensional
import Nyll.AlgebraicCurves.Places.Place_isRational_iff_deg_eq_one
import Nyll.AlgebraicCurves.Places.Place_evalAt_congr
import Nyll.AlgebraicCurves.Places.Place_evalAt_algebraMap

/-!
# Exists is Rational forall mem and eval At eq of alg Hom
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.Exists_isRational_forall_mem_and_evalAt_eq_of_algHom
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve IsLocalRing

theorem _root_.AlgebraicCurve.exists_isRational_forall_mem_and_evalAt_eq_of_algHom
    {L : Type*} [Field L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (B : Subalgebra L F) (χ : B →ₐ[L] L)
    (hB : ∃ z : B, (z : F) ∉ Set.range (algebraMap L F)) :
    ∃ P : Place L F, P.IsRational ∧
      ∀ z : B, (z : F) ∈ P.toValuationSubring ∧ P.evalAt (z : F) = χ z := by
  classical
  obtain ⟨z₀, hz₀⟩ := hB
  let I : Ideal ↥B.toSubring := RingHom.ker (χ.toRingHom : ↥B →+* L)
  have hI : I ≠ ⊤ := RingHom.ker_ne_top (χ.toRingHom : ↥B →+* L)
  obtain ⟨V, hBV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmemI : ∀ z : B, ((z : F) - algebraMap L F (χ z)) ∈ V.nonunits := by
    intro z
    refine hIV ⟨⟨(z : F) - algebraMap L F (χ z), B.sub_mem z.2 (B.algebraMap_mem (χ z))⟩, ?_, rfl⟩
    change (⟨(z : F) - algebraMap L F (χ z), _⟩ : ↥B) ∈ RingHom.ker (χ.toRingHom : ↥B →+* L)
    rw [RingHom.mem_ker]
    change χ (z - algebraMap L (↥B) (χ z)) = 0
    rw [map_sub, AlgHom.commutes]
    simp
  have hVL : ∀ a : L, algebraMap L F a ∈ V := fun a => hBV (B.algebraMap_mem a)
  have hne0 : (z₀ : F) - algebraMap L F (χ z₀) ≠ 0 := fun e => hz₀ ⟨χ z₀, (sub_eq_zero.mp e).symm⟩
  have hVtop : V ≠ ⊤ := by
    intro h
    rcases (ValuationSubring.mem_nonunits_iff_or V).mp (hmemI z₀) with h0 | hinv
    · exact hne0 h0
    · exact hinv (h.symm ▸ ValuationSubring.mem_top _)
  obtain ⟨t, -, hfd, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional (K := L) (F := F)).mp
      inferInstance
  have := hfd
  obtain ⟨P, hP⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional t V hVL
    hVtop
  subst hP
  have hrat : P.IsRational := (Place.isRational_iff_deg_eq_one P).mpr
    (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  refine ⟨P, hrat, fun z => ?_⟩
  have hzV : (z : F) ∈ P.toValuationSubring := hBV z.2
  refine ⟨hzV, ?_⟩
  by_cases hz : (z : F) - algebraMap L F (χ z) = 0
  · rw [sub_eq_zero.mp hz, Place.evalAt_algebraMap]
  · have hmem : (z : F) - algebraMap L F (χ z) ∈ P.toValuationSubring :=
      P.toValuationSubring.sub_mem hzV (P.algebraMap_mem' (χ z))
    have hmax : (⟨_, hmem⟩ : P.toValuationSubring) ∈ maximalIdeal P.toValuationSubring :=
      ValuationSubring.coe_mem_nonunits_iff.mp (hmemI z)
    have hpos : 0 < P.ord ((z : F) - algebraMap L F (χ z)) :=
      (Place.mem_maximalIdeal_iff_ord_pos P hz hmem).mp hmax
    rw [P.evalAt_congr hzV (P.algebraMap_mem' (χ z)) (Or.inr hpos), Place.evalAt_algebraMap]

end AlgebraicCurves.Geometry.Proofs.Exists_isRational_forall_mem_and_evalAt_eq_of_algHom
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
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

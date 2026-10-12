/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.WeilPairing.DivisorialWeilPairingData_toHom_injective_of_divisible_coprime_of_isAlgClosed
import Nyll.JacobianVarieties.Pic0.Pic0_torsion_bijective_of_injective
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Perfection over an algebraically closed field

Combine the proved injectivity with finite torsion duality. The divisibility
hypothesis is retained exactly as supplied by the original theorem.
-/

section ProofImplementation

namespace JacobianVarieties.WeilPairing.Proofs.ClosedFieldPerfectPairing
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one
  AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
  AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  RatFunc.denom_X_pow
  RatFunc.powerBasisAdjoinXPow_dim
  RatFunc.powerBasisAdjoinXPow_gen
  RatFunc.intDegree_X_pow
  RatFunc.num_X_pow

open AlgebraicCurve

with_weak_namespace _root_.AlgebraicCurve.DivisorialWeilPairingData
theorem perfect_of_divisible_coprime_of_isAlgClosed.{u, v}
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] {n : ℕ} [NeZero n] (hn : (n : K) ≠ 0)
    (hdiv : ∀ (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
      [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
      ∀ (m : ℤ), (m : K) ≠ 0 → ∀ x : Pic0 K L', ∃ y, m • y = x)
    [Finite (Pic0.torsion K F n)]
    (e : DivisorialWeilPairingData K F n) : e.Perfect := by
  have : NeZero (n : K) := ⟨hn⟩
  exact Pic0.torsion.bijective_of_injective e.toHom
    (DivisorialWeilPairingData.toHom_injective_of_divisible_coprime_of_isAlgClosed hn hdiv e)
end JacobianVarieties.WeilPairing.Proofs.ClosedFieldPerfectPairing
end ProofImplementation

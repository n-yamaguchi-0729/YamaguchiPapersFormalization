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

import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremK_ratFunc_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Differentials.Uniformizer
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Basic

/-!
# Rational Function Field trace local Residue finite Place add trace local Residue place
Infty eq zero
-/

section ProofImplementation

open _root_.AlgebraicCurves.Differentials.Residues.Proofs
open ResidueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve (
  dX)
open ResidueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve (
  ordDifferentialWellDefined_ratFunc_of_perfectField)
open ResidueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve (
  p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum)
open ResidueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve (
  p1PrincipalPartAtom)

namespace AlgebraicCurve.RationalFunctionField

open _root_.Polynomial

theorem trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))))
      + Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  let Rfam : ∀ v : AlgebraicCurve.Place K (RatFunc K),
      v.CanonicalLocalResidueDataK :=
    fun v => AlgebraicCurve.HasCanonicalLocalResidueKStar.dataKStar v
  let _ : AlgebraicCurve.HasPrincipalDivisors K (RatFunc K) :=
    AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors K
  have hinfty :
      ResidueTheoremK_ratFunc_of_isAlgClosed.AlgebraicCurve.RationalFunctionField.placeInfty K
        = AlgebraicCurve.RationalFunctionField.placeInfty K := by
    rfl
  have h :=
    p0n21_rtk_kaehlerResidueTermKFam_atom_mOne_two_place_sum
      Rfam
      (ordDifferentialWellDefined_ratFunc_of_perfectField K)
      hmon hp hc
  rw [hinfty] at h
  simpa only [AlgebraicCurve.kaehlerResidueTermKFam_apply,
    AlgebraicCurve.diagonalHom_apply,
    AlgebraicCurve.Place.localResidue,
    Rfam,
    dX,
    p1PrincipalPartAtom,
    pow_one] using h

end AlgebraicCurve.RationalFunctionField
end ProofImplementation

open AlgebraicCurve.IsCurveOver in
attribute [-instance]
  instNontrivialKaehler
  instFreeKaehler
  toHasPrincipalDivisors
  instFiniteResidue
open _root_.AlgebraicCurve in
attribute [-instance]
  instFundamentalIdentityOfSumRamificationInertia
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

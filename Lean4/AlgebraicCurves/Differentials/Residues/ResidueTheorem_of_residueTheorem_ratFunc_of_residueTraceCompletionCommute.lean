/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import AlgebraicCurves.Differentials.Residues.FibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Differentials.Uniformizer
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Differentials.Kaehler.Weil
import AlgebraicCurves.Differentials.Residues.TateTrace
import AlgebraicCurves.Differentials.Residues.Construction

/-!
# Differentials, residues, and divisor correspondences

A residue theorem for the rational-function field and completed residue-trace compatibility yield
the extension residue theorem.
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs
namespace ResidueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute

noncomputable section

open _root_.AlgebraicCurve

open FibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates.AlgebraicCurve
  (exists_kaehlerPullback_ne_zero
    residueTheorem_of_fiberKaehlerCotraceResidueIdentity
    fiberKaehlerCotraceResidueIdentity_of_rtcc_cts)
in
theorem
  _root_.AlgebraicCurve.residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
    {K F : Type*} [Field K] [PerfectField K]
    [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [Algebra.IsSeparable (RatFunc K) F]
    [HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    (hP1 : ResidueTheorem K (RatFunc K))
    (hRTCC : ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    ResidueTheorem K F := by
  classical
  obtain ⟨ω₀, hgen⟩ :=
    exists_kaehlerPullback_ne_zero
      (K := K) (F := F) (E := RatFunc K)
  have hω₀ : ω₀ ≠ 0 := by
    intro hzero
    subst hzero
    exact hgen ((KaehlerDifferential.map K K (RatFunc K) F).map_zero)
  apply
    residueTheorem_of_fiberKaehlerCotraceResidueIdentity
      (E := RatFunc K) hP1 hω₀ hgen
  exact
    fiberKaehlerCotraceResidueIdentity_of_rtcc_cts
      (by intro _ _; exact hRTCC)
      (AlgebraicCurve.completionTraceSum_of_isSeparable
        (K := K) (F := F) (E := RatFunc K))

end

end ResidueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
end AlgebraicCurves.Differentials.Residues.Proofs
end ProofImplementation

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualFactor

/-!
# Complete higher-radical factors at a prescribed common exponent

The factorial exponent is only one way to obtain a common multiple of local
ramification indices.  For the absolute Abhyankar argument the useful common
multiple is instead built from the actual ramification indices above a
boundary divisor.  This file keeps the exponent and its divisibility proof
explicit while still constructing the target uniformizer and its unit
decomposition from the complete-DVF data.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uKv uL uLv

/-- A prescribed root whose exponent is divisible by the intrinsic
ramification index produces the actual finite-etale higher-radical factor.

Unlike the degree-factorial wrapper, the target complete valuation is part
of the input.  This is the form consumed by the product of the *actual*
ramification indices over a boundary divisor. -/
theorem exists_higherRadicalActualFactorData_of_completeTarget_of_root
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : CompleteDVF.{uK, uKv} K)
    (target : CompleteDVF.{uL, uLv} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ)
    (hdiv : ramificationIndex base.toDVF target.toDVF ∣ N)
    (beta : AlgebraicClosure L)
    (hbeta :
      beta ^ N =
        algebraMap K (AlgebraicClosure L) (varpi : K)) :
    ∃ (pi : target.valuationSubring)
        (unit : target.valuationSubringˣ),
      target.valuation.IsUniformizer (pi : L) ∧
        integerMap base.toDVF target.toDVF varpi =
          (unit : target.valuationSubring) *
            pi ^ ramificationIndex base.toDVF target.toDVF ∧
        Nonempty
          (HigherRadicalActualFactorData
            base.toDVF target.toDVF varpi N beta) := by
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  obtain ⟨unit, hdecomp⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base.toDVF target.toDVF hvarpi hpi
  refine ⟨pi, unit, hpi, hdecomp, ?_⟩
  exact higherRadicalActualFactorData
    base.toDVF target.toDVF varpi hvarpi pi unit hpi hdecomp
    N hdiv beta hbeta

/-- Non-coordinate form of
`exists_higherRadicalActualFactorData_of_completeTarget_of_root`: a positive
prescribed common exponent also supplies its root in the algebraic closure.
-/
theorem exists_higherRadicalActualFactorData_of_completeTarget
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : CompleteDVF.{uK, uKv} K)
    (target : CompleteDVF.{uL, uLv} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (N : ℕ) (hN : 0 < N)
    (hdiv : ramificationIndex base.toDVF target.toDVF ∣ N) :
    ∃ (pi : target.valuationSubring)
        (unit : target.valuationSubringˣ)
        (beta : AlgebraicClosure L),
      target.valuation.IsUniformizer (pi : L) ∧
        integerMap base.toDVF target.toDVF varpi =
          (unit : target.valuationSubring) *
            pi ^ ramificationIndex base.toDVF target.toDVF ∧
        beta ^ N =
          algebraMap K (AlgebraicClosure L) (varpi : K) ∧
        Nonempty
          (HigherRadicalActualFactorData
            base.toDVF target.toDVF varpi N beta) := by
  obtain ⟨beta, hbeta⟩ :=
    IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure L) (varpi : K)) hN
  obtain ⟨pi, unit, hpi, hdecomp, hfactor⟩ :=
    exists_higherRadicalActualFactorData_of_completeTarget_of_root
      base target varpi hvarpi N hdiv beta hbeta
  exact ⟨pi, unit, beta, hpi, hdecomp, hbeta, hfactor⟩

end EtaleFundamentalGroups.Kummer

end

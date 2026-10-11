/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualFactor

/-!
# A common factorial exponent for complete higher-radical factors

For a family of completed field factors, their local ramification indices
need not be equal.  A single radical cover can nevertheless be used once a
common upper bound for the local field degrees is known: every ramification
index is positive and bounded by its local degree, hence divides the
factorial of the common bound.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w

/-- A degree bound produces an actual finite-étale higher-radical factor at
the common exponent `D.factorial`.

The target valuation, its finite valuation ring, the local ramification
index divisibility, the target uniformizer decomposition, and the prescribed
factorial root are all constructed in the proof. -/
theorem exists_higherRadicalActualFactorData_factorial_of_completeBase
    {K : Type u} {L : Type w} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : CompleteDVF.{u, v} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) (hdegree : Module.finrank K L ≤ D) :
    ∃ target : CompleteDVF.{w, 0} L,
      ∃ hExt : base.valuation.HasExtension target.valuation,
        letI : base.valuation.HasExtension target.valuation := hExt
        let e := ramificationIndex base.toDVF target.toDVF
        ∃ (pi : target.valuationSubring)
            (unit : target.valuationSubringˣ)
            (beta : AlgebraicClosure L),
          target.valuation.IsUniformizer (pi : L) ∧
            integerMap base.toDVF target.toDVF varpi =
              (unit : target.valuationSubring) * pi ^ e ∧
            beta ^ D.factorial =
              algebraMap K (AlgebraicClosure L) (varpi : K) ∧
            Nonempty
              (HigherRadicalActualFactorData
                base.toDVF target.toDVF varpi D.factorial beta) := by
  obtain ⟨target, hExt, hIntegralClosure, hFundamental⟩ :=
    exists_integralClosure_standard_fundamental_identity
      (K := K) (L := L) base
  refine ⟨target, hExt, ?_⟩
  let : base.valuation.HasExtension target.valuation := hExt
  let : IsScalarTower base.valuationSubring target.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L := hIntegralClosure
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_isIntegralClosure
      (K := K) (L := L) base target
  let : Module.IsTorsionFree base.valuationSubring
      target.valuationSubring :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (integerMap_injective base.toDVF target.toDVF)
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  obtain ⟨unit, hdecomp⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base.toDVF target.toDVF hvarpi hpi
  let e := ramificationIndex base.toDVF target.toDVF
  have he : 0 < e := by
    exact Nat.pos_of_ne_zero
      (ramificationIndex_ne_zero (base := base) (target := target))
  have heDegree : e ≤ Module.finrank K L := by
    calc
      e ≤ e * residueDegree base.toDVF target.toDVF :=
        Nat.le_mul_of_pos_right e (residueDegree_pos base target)
      _ = degree base.toDVF target.toDVF := hFundamental.symm
      _ = Module.finrank K L := degree_eq_finrank base.toDVF target.toDVF
  have hdiv : e ∣ D.factorial :=
    Nat.dvd_factorial he (heDegree.trans hdegree)
  obtain ⟨beta, hbeta⟩ :=
    IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure L) (varpi : K))
      (Nat.factorial_pos D)
  refine ⟨pi, unit, beta, hpi, hdecomp, hbeta, ?_⟩
  exact higherRadicalActualFactorData
    base.toDVF target.toDVF varpi hvarpi pi unit hpi hdecomp
    D.factorial hdiv beta hbeta

/-- A prescribed factorial root produces the actual higher-radical factor
over a complete base.

Unlike `exists_higherRadicalActualFactorData_factorial_of_completeBase`, this
form does not choose a new root in the algebraic closure.  It keeps the root
already supplied by a fixed global radical component, while constructing the
target valuation, its finite valuation ring, and the required ramification
divisibility from the degree bound. -/
theorem exists_higherRadicalActualFactorData_factorial_of_completeBase_of_root
    {K : Type u} {L : Type w} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : CompleteDVF.{u, v} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) (hdegree : Module.finrank K L ≤ D)
    (beta : AlgebraicClosure L)
    (hbeta :
      beta ^ D.factorial =
        algebraMap K (AlgebraicClosure L) (varpi : K)) :
    ∃ target : CompleteDVF.{w, 0} L,
      ∃ hExt : base.valuation.HasExtension target.valuation,
        letI : base.valuation.HasExtension target.valuation := hExt
        let e := ramificationIndex base.toDVF target.toDVF
        ∃ (pi : target.valuationSubring)
            (unit : target.valuationSubringˣ),
          target.valuation.IsUniformizer (pi : L) ∧
            integerMap base.toDVF target.toDVF varpi =
              (unit : target.valuationSubring) * pi ^ e ∧
            Nonempty
              (HigherRadicalActualFactorData
                base.toDVF target.toDVF varpi D.factorial beta) := by
  obtain ⟨target, hExt, hIntegralClosure, hFundamental⟩ :=
    exists_integralClosure_standard_fundamental_identity
      (K := K) (L := L) base
  refine ⟨target, hExt, ?_⟩
  let : base.valuation.HasExtension target.valuation := hExt
  let : IsScalarTower base.valuationSubring target.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L := hIntegralClosure
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_isIntegralClosure
      (K := K) (L := L) base target
  let : Module.IsTorsionFree base.valuationSubring
      target.valuationSubring :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (integerMap_injective base.toDVF target.toDVF)
  obtain ⟨pi, hpi⟩ := target.exists_uniformizer
  obtain ⟨unit, hdecomp⟩ :=
    exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
      base.toDVF target.toDVF hvarpi hpi
  let e := ramificationIndex base.toDVF target.toDVF
  have he : 0 < e := by
    exact Nat.pos_of_ne_zero
      (ramificationIndex_ne_zero (base := base) (target := target))
  have heDegree : e ≤ Module.finrank K L := by
    calc
      e ≤ e * residueDegree base.toDVF target.toDVF :=
        Nat.le_mul_of_pos_right e (residueDegree_pos base target)
      _ = degree base.toDVF target.toDVF := hFundamental.symm
      _ = Module.finrank K L := degree_eq_finrank base.toDVF target.toDVF
  have hdiv : e ∣ D.factorial :=
    Nat.dvd_factorial he (heDegree.trans hdegree)
  refine ⟨pi, unit, hpi, hdecomp, ?_⟩
  exact higherRadicalActualFactorData
    base.toDVF target.toDVF varpi hvarpi pi unit hpi hdecomp
    D.factorial hdiv beta hbeta

end EtaleFundamentalGroups.Kummer

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.EtaleFundamentalGroups.Kummer.Henselian.UniformizerDecomposition
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure

/-!
# Actual higher-radical factors over a complete discrete valuation field

For a finite separable extension of a complete discrete valuation field, the
actual integral closure supplies the target complete valuation and the finite
extension of valuation rings.  Consequently the higher-radical actual-factor
construction can be applied at the intrinsic ramification index without
assuming a target valuation ring, its finiteness, a target uniformizer, or a
root in an algebraic closure.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w

/-- A specified uniformizer of a complete DVF has an actual finite-etale
higher-radical factor in every finite separable field extension, at the
intrinsic ramification exponent of the canonical target valuation.

The target complete valuation, finite extension of valuation rings, target
uniformizer and unit decomposition, and the required root in the algebraic
closure are all constructed in the proof. -/
theorem exists_higherRadicalActualFactorData_of_completeBase
    {K : Type u} {L : Type w} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : CompleteDVF.{u, v} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K)) :
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
            beta ^ e =
              algebraMap K (AlgebraicClosure L) (varpi : K) ∧
            Nonempty
              (HigherRadicalActualFactorData
                base.toDVF target.toDVF varpi e beta) := by
  obtain ⟨target, hExt, hIntegralClosure, _hFundamental⟩ :=
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
  obtain ⟨beta, hbeta⟩ :=
    IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure L) (varpi : K)) he
  refine ⟨pi, unit, beta, hpi, hdecomp, hbeta, ?_⟩
  exact higherRadicalActualFactorData
    base.toDVF target.toDVF varpi hvarpi pi unit hpi hdecomp
    e (dvd_refl e) beta hbeta

end EtaleFundamentalGroups.Kummer

end

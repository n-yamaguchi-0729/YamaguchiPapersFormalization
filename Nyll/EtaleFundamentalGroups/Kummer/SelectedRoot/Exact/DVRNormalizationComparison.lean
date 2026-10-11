/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.DegreeSandwich

/-!
# DVR normalization comparison at the exact ramification-index root

For the exact ramification-index root, the degree sandwich identifies the
input DVR extension field `Omega` with the strict-stage chosen component field
`P`. Mapping integral closures along that sourced field equivalence identifies
the input DVR normalization with the normalization of the original DVR inside
`P`.
Since the root ring is integral over the DVR, the integral-base comparison
then identifies this normalization with the chosen root factor `D`.

This is only a height-one DVR coordinate comparison. An Away localization of
the displayed DVR is merely its generic fibre, so this theorem deliberately
does **not** claim the height-two boundary Away statement needed by the final
chosen-factor terminal. That statement must first be lifted through the
height-two finite-etale descent/purity stage.

The integral-closure inputs have concrete producers in the existing chain:

* `exists_etaleChosenLocalFactor_finiteGenericFiberComponent_algEquiv`
  identifies the actual Tag local factor with a prime localization of the
  normalization of the selected component. After the standard fraction-ring
  and integrally-closed localization instances,
  `IsIntegralClosure.of_isIntegrallyClosed` supplies its
  `IsIntegralClosure T V Omega` instance.
* `higherRadicalUnitFactorData_exists_strictHenselian_localizationAlgEquiv`
  produces the retained exact-root local factor. Its domain and finite-etale
  data are supplied by `higherRadicalUnitFactorData_isDomain`,
  `higherRadicalUnitFactorData_radical_finite`, and `factor.radical_etale`;
  taking its fraction ring and applying
  `IsIntegralClosure.of_isIntegrallyClosed` supplies
  `IsIntegralClosure D B P`.
* `lowerUnitFactorHigherBaseChangeFixedComponentRingEquiv` and
  `lowerUnitFactorHigherBaseChangeFixedComponentRingEquiv_root` retain that
  same lower factor and its root coordinate in the later fixed component.

Thus neither integral-closure class is a theorem-shaped comparison assumption.
No field equivalence, degree equality, or comparison equality is an input.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uOmega uW uFroot uT uD uP

/-- Compare the two DVR normalizations at the strict exact-root stage.

The returned equivalence is over the literal valuation subring of `base`.
The field equivalence `Omega ≃ P` is built internally from the exact-root
degree sandwich. This theorem is a local coordinate junction, not the
height-two boundary-Away terminal. -/
noncomputable def
    selectedExactRamificationRoot_DVRNormalizations_algEquiv
    {K : Type uK} {Omega : Type uOmega} {Froot : Type uFroot}
    {T : Type uT} {D : Type uD} {P : Type uP}
    [Field K] [Field Omega] [Field Froot]
    [CommRing T] [CommRing D] [Field P]
    [Algebra K Omega]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    [Algebra base.valuationSubring T]
    [Algebra T Omega]
    [IsScalarTower base.valuationSubring T Omega]
    [IsIntegralClosure T base.valuationSubring Omega]
    [Algebra K Froot]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    [Module.Finite
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    [Algebra.Etale
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    [Algebra base.valuationSubring D]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    (q : Ideal D) [q.IsPrime]
    [q.LiesOver
      (IsLocalRing.maximalIdeal
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    (hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver
        (IsLocalRing.maximalIdeal
          (AdjoinRoot
            (X ^ ramificationIndex base target - C varpi))) →
      Q = q)
    [Algebra D P] [IsFractionRing D P]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D P]
    [IsIntegralClosure D
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    [Algebra Froot P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot P]
    [Algebra K P] [Algebra Omega P]
    [IsScalarTower K Froot P] [IsScalarTower K Omega P]
    [Algebra base.valuationSubring P]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    [IsScalarTower base.valuationSubring D P]
    [IsScalarTower base.valuationSubring Omega P] :
    T ≃ₐ[base.valuationSubring] D := by
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let B := AdjoinRoot (X ^ e - C varpi)
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hFieldBijective : Function.Bijective (algebraMap Omega P) :=
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_strictHenselianChosenFactor
      (K := K) (Omega := Omega) (Froot := Froot) (D := D) (P := P)
      base target varpi hvarpi q hunique
  let fieldEquiv : Omega ≃ₐ[V] P :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom V Omega P)
      hFieldBijective
  let tagEquiv : T ≃ₐ[V] integralClosure V Omega :=
    IsIntegralClosure.equiv V T Omega (integralClosure V Omega)
  let mappedTagEquiv : integralClosure V Omega ≃ₐ[V]
      integralClosure V P := fieldEquiv.mapIntegralClosure
  letI : Module.Finite V B :=
    (monic_X_pow_sub_C varpi he.ne').finite_adjoinRoot
  letI : Algebra.IsIntegral V B := Algebra.IsIntegral.of_finite V B
  letI : Algebra B (integralClosure V P) :=
    integralClosureIntegralBaseAlgebra
  letI : IsScalarTower V B (integralClosure V P) :=
    integralClosureIntegralBase_isScalarTower
  letI : IsScalarTower B (integralClosure V P) P :=
    integralClosureIntegralBase_toAmbient_isScalarTower
  let integralBaseEquiv : integralClosure B P ≃ₐ[B]
      integralClosure V P := integralClosureIntegralBaseAlgEquiv
  let chosenEquiv : integralClosure B P ≃ₐ[B] D :=
    IsIntegralClosure.equiv B (integralClosure B P) P D
  let rootEquivB : integralClosure V P ≃ₐ[B] D :=
    integralBaseEquiv.symm.trans chosenEquiv
  let rootEquivV : integralClosure V P ≃ₐ[V] D :=
    { toRingEquiv := rootEquivB.toRingEquiv
      commutes' := by
        intro a
        rw [IsScalarTower.algebraMap_apply V B (integralClosure V P),
          IsScalarTower.algebraMap_apply V B D]
        exact rootEquivB.commutes (algebraMap V B a) }
  exact (tagEquiv.trans mappedTagEquiv).trans rootEquivV

end EtaleFundamentalGroups.Kummer

end

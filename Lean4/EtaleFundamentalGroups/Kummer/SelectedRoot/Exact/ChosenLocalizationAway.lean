/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ExistsChosenLocalization
import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ExistsChosenLocalizationNoAway
import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ChosenLocalization.Core
import EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.BoundaryAway

/-!
# A boundary-away local factor at the exact ramification root

First choose a closed local factor of the normalization over the strictly
Henselian exact-root ring, using only its finite-etale structure.  Its chosen
component field is already a finite extension of the original fraction field,
so the canonical localization embeds in that same field and has it as fraction
field.  The exact-degree sandwich can therefore be applied to this *already
chosen* factor.  The resulting field comparison transports the original
primitive boundary-away statement, after which the chosen-localization theorem
retains it on the same local factor.

In particular, no away statement for the exact-root cover or its selected
component is an input.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uOmega uW uFroot uP

/-- Etaleness of the normalization over the strictly Henselian exact-root
ring already forces the specified component field to equal `Omega` over the
base field.  A closed local factor is chosen internally, before applying the
exact-degree sandwich. -/
theorem
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_normalization_etale
    {K : Type uK} {Omega : Type uOmega} {Froot : Type uFroot}
    {P : Type uP}
    [Field K] [Field Omega] [Field Froot] [Field P]
    [Algebra K Omega]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
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
    [Module.Finite base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [Algebra.IsIntegral base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    [Algebra K P] [FiniteDimensional K P]
    [Algebra Froot P]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot P]
    [IsScalarTower K Froot P]
    [Algebra Omega P] [IsScalarTower K Omega P]
    [Algebra base.valuationSubring P]
    [IsScalarTower base.valuationSubring K P]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    (hEtale : Algebra.Etale
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))
      (integralClosure
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)) P)) :
    Function.Bijective (algebraMap Omega P) := by
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let B := AdjoinRoot (X ^ e - C varpi)
  let Cnorm := integralClosure V P
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra B Cnorm :=
    EtaleFundamentalGroups.integralClosureIntegralBaseAlgebra
  let : IsScalarTower V B Cnorm :=
    EtaleFundamentalGroups.integralClosureIntegralBase_isScalarTower
  have hChoose :=
    EtaleFundamentalGroups.exists_integralClosure_integralBase_chosenLocalization_finiteEtale_unique
      (A := V) (B := B) (L := P) hEtale
  dsimp only at hChoose
  obtain ⟨q, hqPrime, hqOver, hFinite, hEtaleD,
      hClosedOver, hUnique⟩ := hChoose
  let : q.IsPrime := hqPrime
  let : q.LiesOver (maximalIdeal B) := hqOver
  let D := Localization.AtPrime q
  let : Module.Finite B D := hFinite
  let : Algebra.Etale B D := hEtaleD
  let : IsFractionRing Cnorm P :=
    integralClosure.isFractionRing_of_finite_extension K P
  let : Algebra D P :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra
      (A := Cnorm) (K := P) q
  let : IsScalarTower Cnorm D P :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionField_isScalarTower
      (A := Cnorm) (K := P) q
  let : IsFractionRing D P :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionField_isFractionRing
      (A := Cnorm) (K := P) q
  let : IsScalarTower B Cnorm P :=
    EtaleFundamentalGroups.integralClosureIntegralBase_toAmbient_isScalarTower
  let : IsScalarTower B D P :=
    IsScalarTower.of_algebraMap_eq fun b ↦ by
      calc
        algebraMap B P b =
            algebraMap Cnorm P (algebraMap B Cnorm b) :=
          IsScalarTower.algebraMap_apply B Cnorm P b
        _ = algebraMap D P
            (algebraMap Cnorm D (algebraMap B Cnorm b)) :=
          IsScalarTower.algebraMap_apply Cnorm D P
            (algebraMap B Cnorm b)
        _ = algebraMap D P (algebraMap B D b) := by
          rw [IsScalarTower.algebraMap_apply B Cnorm D b]
  let qD := maximalIdeal D
  let : qD.IsPrime := (IsLocalRing.maximalIdeal.isMaximal D).isPrime
  let : qD.LiesOver (maximalIdeal B) := hClosedOver
  have hUniqueD : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver (maximalIdeal B) → Q = qD := by
    simpa only [qD] using hUnique
  exact
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_strictHenselianChosenFactor
      (K := K) (Omega := Omega) (Froot := Froot)
      (D := D) (P := P)
      base target varpi hvarpi qD hUniqueD

/-- At the exact ramification-index root, a finite-etale normalization has a
closed local factor on which the literal primitive map from the original DVR
is etale away from `f`.

The prime is selected before any boundary-away transport.  The only away
input is the original normalization of `Omega`; the exact-root degree sandwich
identifies `Omega` with the selected component field `P` internally. -/
theorem
    exists_selectedExactRamificationRoot_chosenLocalization_away
    {K : Type uK} {Omega : Type uOmega} {Froot : Type uFroot}
    {P : Type uP}
    [Field K] [Field Omega] [Field Froot] [Field P]
    [Algebra K Omega]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
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
    [Module.Finite base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [Algebra.IsIntegral base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    [Algebra K P] [FiniteDimensional K P]
    [Algebra Froot P]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot P]
    [IsScalarTower K Froot P]
    [Algebra Omega P] [IsScalarTower K Omega P]
    [Algebra base.valuationSubring Omega]
    [IsScalarTower base.valuationSubring K Omega]
    [Algebra base.valuationSubring P]
    [IsScalarTower base.valuationSubring K P]
    [IsScalarTower base.valuationSubring Omega P]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    (hEtale : Algebra.Etale
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))
      (integralClosure
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)) P))
    (f : base.valuationSubring)
    (hAway :
      @RingHom.Etale
        (Localization.Away f)
        (Localization.Away
          (algebraMap base.valuationSubring
            (integralClosure base.valuationSubring Omega) f))
        _ _
        (Localization.awayMap
          (algebraMap base.valuationSubring
            (integralClosure base.valuationSubring Omega)) f)) :
    let B := AdjoinRoot
      (X ^ ramificationIndex base target - C varpi)
    let Cnorm := integralClosure base.valuationSubring P
    letI : Algebra B Cnorm :=
      EtaleFundamentalGroups.integralClosureIntegralBaseAlgebra
    letI : IsScalarTower base.valuationSubring B Cnorm :=
      EtaleFundamentalGroups.integralClosureIntegralBase_isScalarTower
    ∃ (q : Ideal Cnorm) (hqPrime : q.IsPrime)
      (_ : q.LiesOver (maximalIdeal B)),
      letI : q.IsPrime := hqPrime
      let D := Localization.AtPrime q
      letI : CommRing D := inferInstance
      letI : CommRing
          (Localization.Away (algebraMap base.valuationSubring D f)) := inferInstance
      letI : CommSemiring
          (Localization.Away (algebraMap base.valuationSubring D f)) :=
        CommRing.toCommSemiring
      @Algebra.Etale
        (Localization.Away f)
        (Localization.Away (algebraMap base.valuationSubring D f))
        _ _
        (Localization.awayMap
          (algebraMap base.valuationSubring D) f).toAlgebra := by
  dsimp only
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let B := AdjoinRoot (X ^ e - C varpi)
  let Cnorm := integralClosure V P
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : Algebra B Cnorm :=
    EtaleFundamentalGroups.integralClosureIntegralBaseAlgebra
  let : IsScalarTower V B Cnorm :=
    EtaleFundamentalGroups.integralClosureIntegralBase_isScalarTower
  have hbij : Function.Bijective (algebraMap Omega P) :=
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_normalization_etale
      (K := K) (Omega := Omega) (Froot := Froot) (P := P)
      base target varpi hvarpi hEtale
  have hAwayP :
      @RingHom.Etale
        (Localization.Away f)
        (Localization.Away (algebraMap V (integralClosure V P) f))
        _ _
        (Localization.awayMap
          (algebraMap V (integralClosure V P)) f) :=
    EtaleFundamentalGroups.integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := V) hbij f hAway
  have hResult :=
    (open _root_.EtaleFundamentalGroups in
      exists_integralClosure_integralBase_chosenLocalization_finiteEtale_unique_away
        (A := V) (B := B) (L := P) hEtale f hAwayP)
  dsimp only at hResult
  obtain ⟨q, hqPrime, hqOver, hFinite, hEtaleD,
      hClosedOver, hUnique, hAwayD⟩ := hResult
  refine ⟨q, hqPrime, hqOver, ?_⟩
  exact hAwayD

end EtaleFundamentalGroups.Kummer

end

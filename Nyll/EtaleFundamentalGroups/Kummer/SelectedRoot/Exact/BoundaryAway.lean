/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BoundaryAwayFieldEquiv
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.DegreeSandwich

/-!
# Primitive boundary-away transport at the exact ramification root

The exact-root degree sandwich makes the canonical target-field map to the
chosen component bijective.  Mapping integral closures along the resulting
field equivalence transports the primitive boundary-away statement without
assuming a comparison map or a degree equality.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uOmega uW uFroot uD uP

/-- At the exact ramification-index root, strict-Henselian splitting of the
chosen finite-etale factor transports the original normalization's literal
boundary-away map to the selected component field. -/
theorem
    selectedExactRamificationRoot_integralClosure_boundaryAway_of_strictHenselianChosenFactor
    {K : Type uK} {Omega : Type uOmega} {Froot : Type uFroot}
    {D : Type uD} {P : Type uP}
    [Field K] [Field Omega] [Field Froot]
    [CommRing D] [Field P]
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
    [Algebra Froot P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot P]
    [Algebra K P] [Algebra Omega P]
    [IsScalarTower K Froot P] [IsScalarTower K Omega P]
    [Algebra base.valuationSubring Omega]
    [IsScalarTower base.valuationSubring K Omega]
    [Algebra base.valuationSubring P]
    [IsScalarTower base.valuationSubring K P]
    [IsScalarTower base.valuationSubring Omega P]
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
    @RingHom.Etale
      (Localization.Away f)
      (Localization.Away
        (algebraMap base.valuationSubring
          (integralClosure base.valuationSubring P) f))
      _ _
      (Localization.awayMap
        (algebraMap base.valuationSubring
          (integralClosure base.valuationSubring P)) f) := by
  have hbij : Function.Bijective (algebraMap Omega P) :=
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_strictHenselianChosenFactor
      (K := K) (Omega := Omega) (Froot := Froot) (D := D) (P := P)
      base target varpi hvarpi q hunique
  exact
    EtaleFundamentalGroups.integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := base.valuationSubring) hbij f hAway

end EtaleFundamentalGroups.Kummer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.IntegralClosure.BoundaryAwayFieldEquiv
import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ChosenLocalization.Core

/-!
# Boundary-away chosen factors after a field comparison

A bijective map between two ambient fields transports the primitive away
property between their normalizations.  Selecting a local factor only after
that transport then retains the literal composite away map from the original
base.  This separates the field-comparison step from the integral-base
chosen-factor construction.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe uA uB uOmega uP

/-- A sourced field equivalence transports the primitive boundary-away map
to every chosen finite-etale local factor of the target normalization. -/
theorem
    integralClosure_chosenLocalization_finiteEtale_unique_away_of_bijective_fieldTower
    {A : Type uA} {B : Type uB}
    {Omega : Type uOmega} {P : Type uP}
    [CommRing A] [CommRing B] [Field Omega] [Field P]
    [IsNoetherianRing A]
    [HenselianLocalRing B]
    [Algebra A B] [Module.Finite A B]
    [Algebra A Omega]
    [Algebra Omega P] [Algebra A P] [IsScalarTower A Omega P]
    [Algebra B P] [IsScalarTower A B P]
    (hEtale : Algebra.Etale B (integralClosure B P))
    (hbij : Function.Bijective (algebraMap Omega P))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) f).Etale) :
    let C := integralClosure A P
    letI : Algebra B C := integralClosureIntegralBaseAlgebra
    letI : IsScalarTower A B C :=
      integralClosureIntegralBase_isScalarTower
    ∀ (q : Ideal C) [q.IsPrime]
      [q.LiesOver (maximalIdeal B)],
      let D := Localization.AtPrime q
      Module.Finite B D ∧
        Algebra.Etale B D ∧
        (maximalIdeal D).LiesOver (maximalIdeal B) ∧
        (∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (maximalIdeal B) → Q = maximalIdeal D) ∧
        @Algebra.Etale
          (Localization.Away f)
          (Localization.Away (algebraMap A D f))
          _ _
          (Localization.awayMap (algebraMap A D) f).toAlgebra := by
  dsimp only
  let C := integralClosure A P
  let : Algebra B C := integralClosureIntegralBaseAlgebra
  let : IsScalarTower A B C :=
    integralClosureIntegralBase_isScalarTower
  have hAwayP :
      (Localization.awayMap
        (algebraMap A (integralClosure A P)) f).Etale :=
    integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := A) hbij f hAway
  exact
    integralClosure_integralBase_chosenLocalization_finiteEtale_unique_away
      (A := A) (B := B) (L := P) hEtale f hAwayP

end EtaleFundamentalGroups

end

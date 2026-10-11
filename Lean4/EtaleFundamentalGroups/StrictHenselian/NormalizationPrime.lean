/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.SeparablyClosedFractionHenselian
import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integral


/-!
# Strict Henselianity of an actual normalization prime localization

The integral closure in an algebraic separably closed extension has that
extension as its fraction field, by the native algebraic integral-closure
owner. Its literal prime localization is normal and has the same fraction
field through the existing prescribed localization map. The established
separably closed fraction-field theorem therefore proves strict Henselianity.
No finite extension, Noetherianity, or separately chosen local model is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

universe u v w

private theorem primeLocalization_strictHenselian
    (B : Type u) (L : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field L] [Algebra B L] [IsFractionRing B L] [IsSepClosed L]
    (Q : Ideal B) [Q.IsPrime] :
    HenselianLocalRing (Localization.AtPrime Q) ∧
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  have : IsIntegrallyClosed (Localization.AtPrime Q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime Q)
      Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : Algebra (Localization.AtPrime Q) L :=
    localizationAtPrimeToFractionFieldAlgebra (K := L) Q
  have : IsFractionRing (Localization.AtPrime Q) L :=
    localizationAtPrimeToFractionField_isFractionRing (K := L) Q
  exact henselianLocalRing_and_isSepClosed_residueField_of_isSepClosed_fractionRing
    (Localization.AtPrime Q) L

/-- The literal localization of the integral closure at any prime is strictly
Henselian when the ambient algebraic extension is separably closed. The base
need only be a domain with the displayed fraction field; its normality and
localness are not needed for this supplier. -/
theorem integralClosure_localizationAtPrime_strictHenselian
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [Algebra.IsAlgebraic K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    HenselianLocalRing (Localization.AtPrime Q) ∧
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  let C := integralClosure A L
  have : IsFractionRing C L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed C := IsIntegrallyClosed.of_isIntegrallyClosedIn C L
  exact primeLocalization_strictHenselian C L Q

end EtaleFundamentalGroups.StrictHenselian

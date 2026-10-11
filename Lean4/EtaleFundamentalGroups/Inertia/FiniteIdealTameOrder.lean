/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationInertiaCardinality
import ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCardinality
import ValuedFieldTheory.Ramification.HilbertRamification.RingTameOrderRamification
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Tame and wild orders at an original prime

Defines the finite tame and principal-unit kernel orders and factors the inertia cardinality.
Establishes positivity and residue-field invertibility of the tame order.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

variable (B : Type u) [CommRing B] [IsDedekindDomain B]
variable (G : Type v) [Group G] [MulSemiringAction G B]
variable (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)

/-- The actual finite tame degree at the original normalization prime.
Its local DVR and stabilizer action are constructed from that original prime. -/
def finiteIdealTameOrder : ℕ := by
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hQ (Localization.AtPrime Q)
  exact tameOrder (Localization.AtPrime Q) (MulAction.stabilizer G Q)

/-- The actual principal-unit kernel order at that same original prime. -/
def finiteIdealWildOrder : ℕ := by
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hQ (Localization.AtPrime Q)
  exact Nat.card (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q))

/-- The original ideal-inertia order is the product of the actual tame order
and actual principal-unit kernel order. No residue field is opened here. -/
theorem finiteIdealInertia_card_eq_tame_mul_wild :
    Nat.card (Q.inertia G) = finiteIdealTameOrder B G Q hQ * finiteIdealWildOrder B G Q hQ := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hQ (Localization.AtPrime Q)
  change Nat.card (Q.inertia G) =
    tameOrder (Localization.AtPrime Q) (MulAction.stabilizer G Q) *
      Nat.card (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q))
  rw [← SchemeTheory.stabilizerLocalization_inertia_card B G Q]
  exact inertia_card_eq_tameOrder_mul_principalUnitInertia_card
    (Localization.AtPrime Q) (MulAction.stabilizer G Q)

theorem finiteIdealTameOrder_pos [Finite G] : 0 < finiteIdealTameOrder B G Q hQ := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hQ (Localization.AtPrime Q)
  exact tameOrder_pos (Localization.AtPrime Q) (MulAction.stabilizer G Q)

/-- The actual degree at the original prime is invertible in its actual local residue field. -/
theorem finiteIdealTameOrder_isUnit [Finite G] :
    IsUnit (finiteIdealTameOrder B G Q hQ : IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      B hQ (Localization.AtPrime Q)
  exact tameOrder_isUnit_residue (Localization.AtPrime Q) (MulAction.stabilizer G Q)

end EtaleFundamentalGroups.Inertia

end

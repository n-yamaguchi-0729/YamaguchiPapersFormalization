/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import Nyll.SchemeTheory.RingTheory.Localization.DedekindPrime
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationInertiaEquivalence
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingTameQuotientCardinality
import Mathlib.GroupTheory.Index

/-!
# Original ideal inertia quotient cardinality

The actual localization inertia equivalence transports the local tame-image
cardinality to original ideal inertia modulo its independent wild subgroup.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u

/-- The original-prime tame degree is the literal quotient cardinality for
its independently transported principal-unit wild subgroup. -/
theorem finiteIdealTameOrder_eq_card_quotient_wild
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    (G : Type u) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    finiteIdealTameOrder B G Q hQ =
      Nat.card (idealInertiaGroupObject B G Q ⧸ finiteIdealWildSubgroup B G Q hQ) := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  calc
    finiteIdealTameOrder B G Q hQ = Nat.card
        ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia
          (MulAction.stabilizer G Q) ⧸
          principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q)) :=
      tameOrder_eq_card_quotient_principalUnitInertia
        (Localization.AtPrime Q) (MulAction.stabilizer G Q)
    _ = Nat.card
        (idealInertiaGroupObject B G Q ⧸ finiteIdealWildSubgroup B G Q hQ) :=
      (Subgroup.index_map_equiv
        (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q))
        (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q)).symm

end EtaleFundamentalGroups.Inertia

end

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Localization.DedekindPrime
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalTameRootsPowerMap
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Normalized tame characters at finite ideals

Defines the ramification-index-to-tame-order normalization exponent and the resulting canonical
character on finite ideal inertia.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

/-- The actual original-prime e/n normalization exponent. -/
def finiteIdealNormalizationExponent
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) : ℕ :=
  Q.ramificationIdx A / finiteIdealTameOrder B G Q hQ

/-- The canonical e/n-normalized character of the actual original finite
ideal inertia, taking values in its full actual root group. -/
def finiteIdealCanonicalTameCharacterGroupMap
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] (G : Type v) [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
    idealInertiaGroupObject B G Q →*
      localTameRootsGroupObject (Localization.AtPrime Q) (MulAction.stabilizer G Q) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact (localTameRootsPowerGroupMap (Localization.AtPrime Q) (MulAction.stabilizer G Q)
    (finiteIdealNormalizationExponent A B G Q hQ)).comp
      (finiteIdealTameCharacterGroupMap B G Q hQ)

end EtaleFundamentalGroups.Inertia

end
